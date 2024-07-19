/*
 * SemPat Project.
 * 
 * @file AttackTableau.scala
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

 * Pattern abstract classes and traits.
 *
 */

package secant
package tableau

import flang.FLang._
import flang._

import MicroProgram.LMOP


sealed abstract class FacetPredicate (val ex: FExpr) {
    def unary_! : FacetPredicate
}
sealed abstract class FacetPredicateFlow (override val ex: FExpr) extends FacetPredicate (ex: FExpr) {
    def unary_! : FacetPredicateFlow
}
case class FacetPredicateFlowDef (override val ex: FExpr) extends FacetPredicateFlow (ex) {
    override def toString(): String = s"fpred_def(${ex})"
    def unary_! : FacetPredicateFlowDef = FacetPredicateFlowDef(!ex)
}
case class FacetPredicateAddrDep (override val ex: FExpr, check: Option[FExpr] = None) extends FacetPredicateFlow (ex) {
    override def toString(): String = s"fpred_addrdep(${ex})"
    def unary_! : FacetPredicateAddrDep = FacetPredicateAddrDep(!ex)
}
case class FacetPredicateDataDep (override val ex: FExpr, check: Option[FExpr] = None) extends FacetPredicateFlow (ex) {
    override def toString(): String = s"fpred_datadep(${ex})"
    def unary_! : FacetPredicateDataDep = FacetPredicateDataDep(!ex)
}
// SameAddr and DiffAddr are negations of each other
case class FacetPredicateSameAddr (override val ex: FExpr, check: Option[FExpr] = None) extends FacetPredicateFlow (ex) {
    override def toString(): String = s"fpred_sameaddr(${ex})"
    def unary_! : FacetPredicateDiffAddr = FacetPredicateDiffAddr(!ex)
}
case class FacetPredicateDiffAddr (override val ex: FExpr, check: Option[FExpr] = None) extends FacetPredicateFlow (ex) {
    override def toString(): String = s"fpred_sameaddr(${ex})"
    def unary_! : FacetPredicateSameAddr = FacetPredicateSameAddr(!ex)
}


sealed abstract class FacetPredicateIF (override val ex: FExpr) extends FacetPredicate (ex: FExpr) {
    def unary_! : FacetPredicateIF
}
case class FacetPredicateIFDef (override val ex: FExpr) extends FacetPredicateIF (ex) {
    override def toString(): String = s"fpred_ifdefault(${ex})"
    def unary_! : FacetPredicateIFDef = FacetPredicateIFDef(!ex)
}
case class FacetPredicateIFHighAddr (override val ex: FExpr) extends FacetPredicateIF (ex) {
    override def toString(): String = s"fpred_lowaddr(${ex})"
    def unary_! = SemPatDriver.ERROR(s"Cannot negate ${this}")
}
case class FacetPredicateIFHighOps (override val ex: FExpr) extends FacetPredicateIF (ex) {
    override def toString(): String = s"fpred_highops(${ex})"
    def unary_! = SemPatDriver.ERROR(s"Cannot negate ${this}")
}
case class FacetPredicateIFHighResult (override val ex: FExpr) extends FacetPredicateIF (ex) {
    override def toString(): String = s"fpred_highres(${ex})"
    def unary_! = SemPatDriver.ERROR(s"Cannot negate ${this}")
}


sealed abstract class TableauAtom
case class TableauFlowEdge(name : String, from: MicroOp, to: MicroOp) extends TableauAtom {
    override def toString(): String = s"${from} -- ${name} -> ${to}"
}
object TableauFlowEdge {
    def apply(from: MicroOp, to: MicroOp) : TableauFlowEdge = 
        TableauFlowEdge(s"default_flowedge_${from}_${to}", from, to)
    def apply(self: LMOP) : TableauFlowEdge = 
        TableauFlowEdge(s"default_feself_${self._2}", self._2, self._2)
}

case class TableauIFLabel(name: String, mop: MicroOp) extends TableauAtom {
    override def toString(): String = s"${name}(${mop})"
}
object TableauIFLabel {
    def apply(mop: MicroOp) : TableauIFLabel = 
        TableauIFLabel(s"default_secatom_${mop}", mop)
}

sealed abstract class TableauSpecification
case class FlatTableauSpecification (name: String, facets: Map[MicroOp, List[FLocalParam]], 
    spec: Annotation, grammar: TableauGrammar) extends TableauSpecification {
    override def toString(): String = {
        s"FlatTableauSpecification(${name})"
    }
}
case class FlowTableauSpecification (name: String, edges: Map[TableauFlowEdge, (Int, Int) => FacetPredicate], 
    iflabels : Map[TableauIFLabel, (Int) => FacetPredicateIF], spec: Annotation, 
    depth: Int = Tableau.maxDepth, wneg: Boolean = false) extends TableauSpecification {
    override def toString(): String = {
        s"FlowTableauSpecification(${name})"
    }
}
case class TreeTableauSpecification (name: String, edges: Map[TableauFlowEdge, (Int, Int) => FacetPredicate], 
    iflabels : Map[TableauIFLabel, (Int) => FacetPredicateIF], spec: Annotation, 
    depth: Int = Tableau.maxDepth, wneg: Boolean = false) extends TableauSpecification {
    override def toString(): String = {
        s"TreeTableauSpecification(${name})"
    }
}

case class TreeTableauSpecificationMultiCon (name: String, edges: Map[TableauFlowEdge, (Int, Int) => FacetPredicate], 
    iflabels : Map[TableauIFLabel, (Int) => FacetPredicateIF], spec: Annotation,
    depth: Int = Tableau.maxDepth, wneg: Boolean = true) extends TableauSpecification {
    override def toString(): String = {
        s"TreeTableauSpecificationMultiCon(${name})"
    }
}


abstract class AbsTableau {
    val tableauSeq : List[LMOP]
    val ninterf : List[List[MicroOp]]
    val predicates : List[FacetPredicate]

    def getPredicateExpressionsAll () : FExpr = predicates.map(_.ex).fold(trueLit)(_ && _)
    def getPredicateExpressionsDef () : FExpr = 
        predicates.map(
            _ match {
                case FacetPredicateFlowDef(ex) => Some(ex)
                case FacetPredicateAddrDep(ex, check) => check
                case FacetPredicateDataDep(ex, check) => check
                case FacetPredicateSameAddr(ex, check) => check
                case FacetPredicateDiffAddr(ex, check)  => check
                case _ => SemPatDriver.ERROR(s"Found IF facet in edge predicates: ${this}!")
            }).flatten.fold(trueLit)(_ && _)
}
/**
  * A tableau is a sequence of micro-operations that can result in transmission 
  * of information from the source to the target.
  *
  * @param tableauSeq : List of micro-operations in the Tableau
  * @param predicate : Predicate that must be satisfied for the tableau to be valid
  */
case class FlatTableau (tableauSeq : List[LMOP], ninterf: List[List[MicroOp]], 
    predicates : List[FacetPredicate], hyperexprs : List[FacetPredicateIF]) extends AbsTableau {
    override def toString(): String = {
        s"FlatTableau(${tableauSeq.map(_._2).mkString(" -> ")})" + 
            " with predicates { " + predicates.map(_.toString()).mkString(", ") +
            " } and iflabels { " + hyperexprs.map(_.toString).mkString(", ") + 
            " } and with interference sequence { " + 
                ninterf.map(_.map(_.toString).mkString(", ")).mkString(" ; ") + " }\n"
    }
 
    def length () = tableauSeq.length

    def extend (mops: List[MicroOp], mop: MicroOp) : FlatTableau = {
        val lmop = (tableauSeq.length, mop)
        val newTransmitSeq = lmop :: tableauSeq
        FlatTableau(newTransmitSeq, mops::ninterf, predicates, hyperexprs)
    }

    def addFacetPredicate (fpred: FacetPredicate) : FlatTableau = {
        FlatTableau(tableauSeq, ninterf, fpred::predicates, hyperexprs)
    }
    def addFacetPredicates (fpreds: List[FacetPredicate]) : FlatTableau = {
        FlatTableau(tableauSeq, ninterf, fpreds ++ predicates, hyperexprs)
    }

    def addHyperExprs (exprs: List[FacetPredicateIF]) : FlatTableau = {
        FlatTableau(tableauSeq, ninterf, predicates, hyperexprs ++ exprs)
    }

    def checkValid (secanno: Annotation, platform: MicroPlatform with HasState) = {
        FunctionalSolver.getTwoSafetyCheck(platform, secanno, 
            LabeledMicroSequence(tableauSeq.map(a => LabeledMicroInstr(a._1, a._2))), 
            Utils.hardenLabeledVarExpr(getPredicateExpressionsAll()),
            hyperexprs.map(a => Utils.hardenLabeledVarExpr(a.ex))
        )
    }

    def checkValidSNI (secanno: SpeculativeNIAnnotation, platform: MicroPlatform with HasState with HasSpecFlag, spec: Boolean) = {
        FunctionalSolver.getTwoSafetyCheckNISpeculative(platform, secanno, 
            LabeledMicroSequence(tableauSeq.map(a => LabeledMicroInstr(a._1, a._2))), 
            Utils.hardenLabeledVarExpr(getPredicateExpressionsAll()),
            hyperexprs.map(a => Utils.hardenLabeledVarExpr(a.ex)), spec
        )
    }
}
case class FlowTableau (tableauSeq : List[LMOP], ninterf : List[List[MicroOp]], predicates: List[FacetPredicate],
    hyperexprs: List[FacetPredicateIF], edges: List[TableauFlowEdge], iflabels: List[TableauIFLabel]) extends AbsTableau {
    override def toString(): String = {
        s"FlowTableau(" + {
            if (edges.isEmpty) "noflow" 
            else s"${edges.head.from}${edges.map(fl => s" --${fl.name}-> ${fl.to}").mkString("")}"
        } +
        ") with predicate { " + predicates.map(_.toString()).mkString(", ") + 
        " } and iflabels { " + iflabels.map(_.toString).mkString(", ") + 
        " } and with interference sequence { " + 
            ninterf.map(_.map(_.toString).mkString(", ")).mkString(" ; ") + " }\n"      
    }
 
    def length () = tableauSeq.length

    def addFacetPredicate (fpred: FacetPredicate) : FlowTableau = {
        FlowTableau(tableauSeq, ninterf, fpred::predicates, hyperexprs, edges, iflabels)
    }
}

case class TreeTableau (tableauSeq : List[LMOP], ninterf: List[List[MicroOp]], 
    predicates: List[FacetPredicate], edges: List[(TableauFlowEdge, Int, Int)]) extends AbsTableau {
    override def toString(): String = {
        s"TreeTab with " + "nodes { " + tableauSeq.mkString(", ") +
        " } and constraints { " + predicates.map(_.toString()).mkString(", ") + 
        " } and edges { " + edges.map(d => s"${d._2} ${d._1} ${d._3}").mkString(" && ") + " }\n"
    }
 
    def length () = tableauSeq.length

    def addFacetPredicate (fpred: FacetPredicate) : TreeTableau = {
        TreeTableau(tableauSeq, ninterf, fpred::predicates, edges)
    }
}

object Tableau {

    val maxDepth : Int = 3
    // Need a vocabulary for the tableau gadget
    // A tableau identifies state that can be mentioned from the source and target instructions
    
    // Example1: Spectre v1
    // key insight: that lower the level of the vocabulary, the more expressive the language but the harder it is to check the property
    
    
    // Level 1 (less detailed): HWSW contracts: that state is the address of the second instruction 
    //  (which should match the data value of the first instructions)

    // Level 2 (more detailed): lower than would be a tag match (on the cache lines that are changed)
    // Need a way to generate the tableau gadget
}

sealed abstract class TableauGrammar
case class TGChain (mops: Set[MicroOp], pre: TableauGrammar) extends TableauGrammar {
    def >>> (mops: Set[MicroOp]) = TGChain(mops, this)
}
case class TGEps () extends TableauGrammar {
    def >>> (mops: Set[MicroOp]) = TGChain(mops, this)
}

