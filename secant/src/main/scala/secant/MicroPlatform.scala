/*
 * SemPat Project.
 * 
 * @file MicroPlatform.scala
 *
 * Copyright (c) 2023-24.
 * Adwait Godbole.
 *
 * All Rights Reserved.
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * 1. Redistributions of source code must retain the above copyright notice,
 *
 * this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 *
 * documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its
 * contributors may be used to endorse or promote products derived from this
 * software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * Author: Adwait Godbole
 *
 */


package secant

import scala.collection.mutable.HashMap
import scalax.collection.Graph
import scalax.collection.edge.LDiEdge
import scalax.collection.io.dot._
import implicits._
import scalax.collection.edge.LkDiEdge

import Utils.labMopToString
import MicroProgram.LMOP

import edu.mit.csail.sdg.ast.Expr
import edu.mit.csail.sdg.ast.Sig
import secant.flang.{FType, FFunc, FGlobalParam, FLang}

trait HasState {
    val stateVars : List[FGlobalParam]
    val ufuncs : List[FFunc]
    val customTypes : List[FType]
    val archState : List[FGlobalParam] = List()
}

trait HasSpecFlag {
    // Is speculation enabled for this platform
    val spec_on = FGlobalParam("spec_on", FLang.booleant)
    // Received signal to move into speculating mode?
    val spec = FGlobalParam("spec", FLang.booleant)
    // Is the platform currently speculating?
    val is_spec = spec_on && spec
}

abstract class MicroPlatform {
    
    val mstructs : List[MicroStructure]
    val connections : List[OpPath]

    /**
      * Create a graph from the connections.
      * This is a directed graph with labelled edges.
      *
      * @return Graph[MicroStructure, LkDiEdge]
      */
    def getGraph () : Graph[MicroStage, LkDiEdge] = {
        val allEdges = connections.flatMap(
            conn => {
                val pairs = conn.path.length match {
                    case 1 => List((conn.path(0), MicroStage("BOT")))
                    case _ => (conn.path zip conn.path.tail)
                }
                pairs.map(pair => LkDiEdge(pair._1, pair._2)(conn.mop))
            }
        )
        val g = Graph.from(Nil, allEdges)
        g
    }
    /**
      * Create a dot file for the corresponding layout graph.
      *
      * @return
      */
    def getDotFile () : String = {
        val dotRoot : DotRootGraph = DotRootGraph(
            directed  = true,
            id        = Some("Platform"),
            attrStmts = List(DotAttrStmt(Elem.node, List(DotAttr("shape", "record")))),
            attrList  = List(DotAttr("attr_1", """"one""""),
                            DotAttr("attr_2", "<two>")))
        def edgeTransformer(innerEdge: Graph[MicroStage,LkDiEdge]#EdgeT): Option[(DotGraph,DotEdgeStmt)] = 
            innerEdge.edge match {
                case LkDiEdge(source, target, label) => label match {
                    case label: MicroOp => Some(
                        (dotRoot, DotEdgeStmt(source.toString, target.toString,
                            List(DotAttr("label", label.toString)))))
            }}
        getGraph().toDot(dotRoot, edgeTransformer)
    }

    // Get the list of micro-structures that a micro-op visits.
    def getAllStructures (mop : MicroOp) : List[MicroStructure] = {
        val stages = getAllStages(mop)
        mstructs.filter(ms => ms.events.forall(e => stages.contains(e)))
    }
    def getAllStages (mop: MicroOp) : List[MicroStage] = {
        connections.filter(c => (c.mop == mop)).flatMap(c => c.path).distinct
    }
    // Get all the micro-events for a program.
    def getAllEvents (mprog: LabeledMicroProgram) : List[MicroEvent] = {
        mprog match {
            case LabeledMicroBranch(lab, mop, thenBranch, elseBranch, f) => getAllStages(mop).map(s => MicroEvent(lab, mop, s)) ++ getAllEvents(thenBranch) ++ getAllEvents(elseBranch)
            case LabeledMicroInstr(lab, mop, f) => getAllStages(mop).map(s => MicroEvent(lab, mop, s))
            case LabeledMicroSequence(ops) => ops.map(i => getAllEvents(i)).flatten
        }
    }
    def getAllEvents (mops : List[MicroOp]) : List[MicroEvent] = {
        getAllEvents(LabeledMicroSequence((mops zip (0 to mops.length)).map(mi => LabeledMicroInstr(mi._2, mi._1, Map()))))
    }
    
    def getAllMicroOps : List[MicroOp] = {
        connections.map(_.mop).distinct
    }
}


// A stage (inside a microstructure)
case class MicroStage(name: String) {
    override def toString() = name
}
// Event: (minstr, stage) pair
case class MicroEvent(lab: Int, mop: MicroOp, st: MicroStage) {
    override def toString() = s"${labMopToString(lab, mop)}_${st}"
}

sealed abstract class OConstraint
case class Ordering(ev1: MicroEvent, ev2: MicroEvent) extends OConstraint
case class CondOrdering(o1: Ordering, o2: Ordering) extends OConstraint


abstract class MicroStructure() {
    def events : List[MicroStage]
    def orderings (lmops: List[LMOP]) : List[OConstraint]
}
/**
 * Enforces particular order of generation.
 * Order of generation is aligned with program order.
 *
 * @param _event
 * @return
 */
case class Generator(_event: MicroStage) extends MicroStructure {
    override def events = List(_event)
    
    override def orderings(lmops: List[LMOP]): List[Ordering] = {
        (lmops zip lmops.tail).map(a => 
            Ordering(MicroEvent(a._1._1, a._1._2, events(0)), MicroEvent(a._2._1, a._2._2, events(0))))
    }
}
/**
 * Pipeline: only intra-ordering is enforced (inter-instruction re-ordering is possible).
 *
 * @param _event
 * @return
 */
case class Pipeline(_events : List[MicroStage]) extends MicroStructure {
    require(events.size == 2, "Pipeline must have exactly 2 stages")

    override def events = _events
    
    override def orderings(lmops: List[LMOP]): List[OConstraint] = {
        // only intra-instruction ordering is enforced
        lmops.map(in => Ordering(MicroEvent(in._1, in._2, events(0)), MicroEvent(in._1, in._2, events(1))))
    }
}
/**
 * FIFO Pipeline: (orders all events internally as FIFO).
 *
 * @param _events
 */    
case class FIFOPipeline(_events: List[MicroStage]) extends MicroStructure {
    require(_events.size == 2, "FIFOPipeline must have exactly 2 stages")

    override def events = _events
    
    override def orderings(lmops: List[LMOP]): List[OConstraint] = {
        val intra = lmops.map(in => Ordering(MicroEvent(in._1, in._2, events(0)), MicroEvent(in._1, in._2, events(1))))
        val inter = lmops.map(in1 => lmops.map(in2 => CondOrdering(
                Ordering(MicroEvent(in1._1, in1._2, events(0)), MicroEvent(in2._1, in2._2, events(0))),
                Ordering(MicroEvent(in1._1, in1._2, events(1)), MicroEvent(in2._1, in2._2, events(1)))
            ))).flatten
        inter ++ intra
    }
}
/**
  * A functional unit does not enforce any requirements on the ordering of events.
  * 
  * @param _event
  */
case class Functional(_event: MicroStage) extends MicroStructure {
    override def events = List(_event)
    override def orderings(lmops: List[LMOP]): List[Ordering] = List()
}
/**
  * A sink (final stage in the life cycle of each instruction).
  *
  * @param _event: represents the event name
  */
case class Sink(_event: MicroStage) extends MicroStructure {
    override def events: List[MicroStage] = List(_event)
    override def orderings(lmops: List[LMOP]): List[OConstraint] = List()
}


// Used to statically determine flow of events for micro-operations
case class OpPath (mop: MicroOp, path: List[MicroStage]) {
    def >>>(next: MicroStage) : OpPath = OpPath(mop, path :+ next)
    override def toString() = s"${mop} :: ${path.mkString(" -> ")}"
}
