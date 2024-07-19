/*
 * SemPat Project.
 * 
 * @file OrderingSolver.scala
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

// Alloy solver
import edu.mit.csail.sdg.ast._
import edu.mit.csail.sdg.translator.A4Options
import edu.mit.csail.sdg.alloy4.A4Reporter.NOP
import edu.mit.csail.sdg.ast.Sig.{PrimSig,UNIV,SubsetSig}
import edu.mit.csail.sdg.alloy4.Util
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod

import scala.collection.JavaConverters._
import java.util.Collection
import java.{util => ju}

// DZuffereys Scala SMT solver
import dzufferey.smtlib.{Formula, Variable, Int, Lt, Implies, Eq, And, Solver, QF_LIA, Sat}
import scala.collection.mutable.MutableList
import dzufferey.smtlib.IntLit
import dzufferey.smtlib.Literal

abstract class OrderingSolverGeneric {
    def solvePlatform (platform: MicroPlatform, mops : List[MicroOp]) : List[List[Tuple2[MicroEvent, MicroEvent]]]
}
abstract class OrderingSolver[S, E] extends OrderingSolverGeneric {

    type Edge = Tuple2[S, S]

    val limit : Int = 10

    def addNode (name : String) : S
    def addEdge (e: Edge) : E
    def addCondEdge (e1: Edge, e2: Edge) : E
    def fuseNodes (s1: S, s2: S) : E
    def solve (constr: List[E], sigs: List[S]) : List[List[Tuple2[S, S]]] 

    def createNodeAtoms (platform: MicroPlatform, mops: List[MicroOp]) : Map[MicroEvent, S] = {
        val nas = platform.getAllEvents(mops).map(a => Tuple2(a, addNode(a.toString()))).toMap
        nas
    }
    def addConstraints (platform: MicroPlatform, mops : List[MicroOp], events: Map[MicroEvent, S]) : List[E] = {
        val instrs = ((mops zip (0 to mops.length)).map(mi => (mi._2, mi._1)))
        val constraints = platform.mstructs.map(ms => ms.orderings(instrs.filter(i => (platform.getAllStructures(i._2).contains(ms))))).flatten
        constraints.map(c => c match {
            case Ordering(ev1, ev2) => {
                addEdge((events(ev1), events(ev2)))
            }
            case CondOrdering(o1, o2) => {
                addCondEdge((events(o1.ev1), events(o1.ev2)), (events(o2.ev1), events(o2.ev2)))
            }
        })
    }

    override def solvePlatform (platform: MicroPlatform, mops : List[MicroOp]) : List[List[Tuple2[MicroEvent, MicroEvent]]] = {
        val events : Map[MicroEvent, S] = createNodeAtoms(platform, mops)
        val cons = addConstraints(platform, mops, events)
        val orderings = solve(cons, events.values.toList)
        val inverseEvents = events.map(_.swap)
        orderings.map(r => 
            r.map(e => Tuple2(inverseEvents(e._1), inverseEvents(e._2)))
        )
    }
}


object AlloyInterface extends OrderingSolver[Sig, Expr] {

    val opt     = new A4Options()
    opt.solver = A4Options.SatSolver.SAT4J
    val absNode = new PrimSig("absNode", Attr.ABSTRACT)
    val hbOrder = absNode.addField("hb", absNode.setOf())

    def addNode (name : String) : Sig = {
        new PrimSig(name, absNode, Attr.ONE)
    }
    def addEdge (e: Edge) : Expr = {
        e._1.product(e._2).in(hbOrder)
    }
    def addCondEdge (e1: Edge, e2: Edge) : Expr = {
        addEdge(e1).implies(addEdge(e2))
    }
    def fuseNodes (s1: Sig, s2: Sig) : Expr = {
        s1.equal(s2)
    }

    def solve (cons: List[Expr], sigs: List[Sig]) = {
        // Irreflexivity constraint
        val constr = cons.reduceRight((b, expr) => expr.and(b))
        val noCycles = hbOrder.closure().intersect(ExprConstant.IDEN).no()

        // TODO: need to ensure that the Integer bound is adequate
        val bound = math.log(sigs.length).toInt + 1
        val cmd = new Command(false, bound, bound, 0, constr.and(noCycles))
        var sol = TranslateAlloyToKodkod.execute_command(NOP, (sigs:+absNode).asJava, cmd, opt)
        val orderings : MutableList[MutableList[(Sig, Sig)]] = MutableList()
        var count = 0
        while (sol.satisfiable() && count < limit) {
            val relations : MutableList[(Sig, Sig)] = MutableList()
            sol.eval(hbOrder).forEach(t => relations.+=:(t.sig(0), t.sig(1)))
            orderings.+=:(relations)
            sol = sol.next()
            count += 1
        }
        orderings.toList.map(l => l.toList)
    }
}

object ZuffereySMTOrderingInterface extends OrderingSolver[Variable, dzufferey.smtlib.Formula] {

    val solver = Solver(QF_LIA)

    def addNode (name : String) : Variable = {
        Variable(name).setType(Int)
    }
    def addEdge (e: Edge) : Formula = {
        //  e._1 < e._2
        Lt(e._1, e._2)
    }
    def addCondEdge (e1: Edge, e2: Edge) : Formula = {
        // addEdge(e1) ==> addEdge(e2)
        Implies(addEdge(e1), addEdge(e2))   
    }
    def fuseNodes (s1: Variable, s2: Variable) : Formula = {
        Eq(s1, s2)
    }

    def solve (cons: List[Formula], sigs: List[Variable]) = {
        val constr = cons.reduceRight((b, expr) => And(b, expr))
        solver.assert(constr)
        val result = solver.checkSat match { 
            case Sat(_) => {
                val model = solver.getPartialModel match { 
                    case Some(m) => {
                        val assigns = sigs.map(s => solver.getValue(s) match {
                            case Some(l) => (s, l(0)._2 match {
                                case Literal(value) => value match {
                                    case v: Int => v
                                    case v: Long => v.toInt
                                    case other => 0
                                }
                                case _ => 0
                            })
                            case None => (s, 0)
                        }).toMap
                        val orderings : MutableList[(Variable, Variable)] = MutableList()
                        for (s1 <- sigs) {
                            for (s2 <- sigs) {
                                if (s1 != s2) {
                                    if (assigns(s1) < assigns(s2)) {
                                        orderings.+=:(s1, s2)
                                    }
                                }
                            }
                        }
                        List(orderings.toList)
                    }
                    case None => {
                        val orderings : MutableList[(Variable, Variable)] = MutableList()
                        List(orderings.toList)
                    }
                }
                model
            }
            case _ => {
                val orderings : MutableList[(Variable, Variable)] = MutableList()
                List(orderings.toList)
            }
        }
        solver.exit
        result
    }
}