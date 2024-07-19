/*
 * SemPat Project.
 * 
 * @file FBoolExprAnalyzer.scala
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
 * AST-based static analysis for Flang expressions and programs.
 *
 */

package secant

package flang

import qmm.qmm

object FBoolExprAnalyzer {

    /**
      * Check if the expression is a propositional expression.
      * Only boolean operators, literals and FId (for propositional variables)
      * are allowed.
      *
      * @param expr
      * @return
      */
    def checkPropositionalExpr (expr: FExpr) : Boolean = {
        expr match {
            case FOpExpr(a, b) => a match {
                case FOr() | FNot() | FAnd() => b.forall(checkPropositionalExpr(_))
                case _ => false
            }
            case FBoolLit(_) | FId(_) => true
            case _ => false
        }
    }

    /**
      * Does best effort parse of the expression as a Boolean expression.
      * For terms that are no more of the Boolean type, it replaces them
      * with an atom.
      *
      * @param cons
      * @return
      */
    def getAllAtoms (cons: FExpr) : Set[FExpr] = {
        cons match {
            case FOpExpr(a, b) => a match {
                case FOr() | FNot() | FAnd() => b.map(getAllAtoms).flatten.toSet
                case _ => Set(cons)
            }
            case FBoolLit(b) => Set()
            case _ => Set(cons)
        }
    }

    /**
      * Build an expression replace the atoms with fresh propositional variables.
      * Do this for general expressions.
      *
      * @param expr
      * @param propmap
      * @return
      */
    def skeletonizeGeneral (expr: FExpr, propmap: Map[FExpr, FId]) : FExpr = {
        expr match {
            case FOpExpr(a, b) => a match {
                case FOr() | FNot() | FAnd() => FOpExpr(a, b.map(skeletonizeGeneral(_, propmap)))
                case _ => propmap.get(expr) match {
                    case Some(prop) => prop
                    case None => throw new Exception("Proposition not found")
                }
            }
            case FBoolLit(b) => expr
            case _ => propmap.get(expr) match {
                case Some(prop) => prop
                case None => throw new Exception("Proposition not found")
            }
        }
    }
    def deskeletonizeGeneral (expr: FExpr, revpropmap: Map[FExpr, FExpr]) : FExpr = {
        expr match {
            case FOpExpr(a, b) => a match {
                case FOr() | FNot() | FAnd() => FOpExpr(a, b.map(deskeletonizeGeneral(_, revpropmap)))
                case _ => revpropmap.get(expr) match {
                    case Some(prop) => prop
                    case None => throw new Exception("FId not found")
                }
            }
            case FBoolLit(b) => expr
            case _ => revpropmap.get(expr) match {
                case Some(prop) => prop
                case None => throw new Exception("Proposition not found")
            }
        }
    }


    def getCNF (expr: FExpr) : Option[List[List[(FExpr, Boolean)]]] = {
        expr match {
            case FOpExpr(a, b) => a match {
                case FOr() => {
                    val disjs = b.map(getCNF(_))
                    disjs.forall(_.isDefined) match {
                        case true => Some(disjs.flatten.flatten)
                        case false => None
                    }
                }
                case FAnd() => getConjunct(expr) match {
                    case Some(conj) => Some(List(conj))
                    case None => None
                }
                case FNot() => b(0) match {
                    case FId(_) => Some(List(List((b(0), false))))
                    case FBoolLit(b) => b match {
                        case true => Some(List(List((FBoolLit(false), true))))
                        case false => Some(List(List((FBoolLit(true), true))))
                    }
                    case _ => None
                }
                case _ => None
            }
            case FBoolLit(_) | FId(_) => Some(List(List((expr, true))))
            case _ => None
        }
    }
    def getConjunct (expr: FExpr) : Option[List[(FExpr, Boolean)]] = {
        expr match {
            case FOpExpr(a, b) => a match {
                case FAnd() => {
                    val conjs = b.map(getConjunct(_))
                    conjs.forall(_.isDefined) match {
                        case true => Some(conjs.flatten.flatten)
                        case false => None
                    }
                }
                case FNot() => b(0) match {
                    case FId(_) => Some(List((b(0), false)))
                    case FBoolLit(b) => b match {
                        case true => Some(List((FBoolLit(false), true)))
                        case false => Some(List((FBoolLit(true), true)))
                    }
                    case _ => None
                }
                case _ => None
            }
            case FBoolLit(_) | FId(_) => Some(List((expr, true)))
            case _ => None
        }
    }
    def elimLiterals (cnf: List[List[(FExpr, Boolean)]]) : List[List[(FExpr, Boolean)]] = {
        cnf.filter(conj => !conj.contains((FBoolLit(false), true))).map(
            _.filter(_ != (FBoolLit(true), true))
        )
    }
    /**
      * Brute force checking of minterm reductions.
      * Can be optimized/simplified in the future.
      *
      * @param cnf
      * @return
      */
    def reduction (cnf: List[List[(FExpr, Boolean)]]) : List[List[(FExpr, Boolean)]] = {
        def checkRed (c1: List[(FExpr, Boolean)], c2: List[(FExpr, Boolean)]) : List[List[(FExpr, Boolean)]] = {
            val cm1 = c1.toMap
            val cm2 = c2.toMap
            val keys1 = cm1.keys.toSet
            val keys2 = cm2.keys.toSet
            if (keys1.equals(keys2)) {
                val diff = (c1.toSet diff c2.toSet).toList
                if (diff.size == 1) {
                    val e = diff.toList(0)._1
                    List(c1.filter(_._1 != e))
                } else List(c1, c2)
            } else if (keys1.subsetOf(keys2)) {
                if (keys1.forall(k => cm1(k) == cm2(k))) List(c1)
                else List(c1, c2)
            } else if (keys2.subsetOf(keys1)) {
                if (keys2.forall(k => cm1(k) == cm2(k))) List(c2)
                else List(c1, c2)
            } else {
                List(c1, c2)
            }
        }

        var reduced = true
        var newcnf = cnf
        while (reduced) {
            reduced = false
            var currcnf : List[List[(FExpr, Boolean)]] = List()
            for (i <- 0 until newcnf.length) {
                for (j <- i+1 until newcnf.length) {
                    if (!reduced) {
                        val newConjs = checkRed(newcnf(i), newcnf(j))
                        if (newConjs.length == 1) {
                            currcnf = newcnf.patch(i, List.empty, 1).patch(j-1, List.empty, 1).++(newConjs)
                            reduced = true
                        }
                    }
                }
            }
            if (reduced) {
                newcnf = currcnf
            }
        }
        newcnf
    }

    /**
      * Brute force checking of minterm reductions.
      * Can be optimized/simplified in the future.
      *
      * @param cnf
      * @return
      */
    def applyqmm (cnf: List[List[(FExpr, Boolean)]], patoms: List[FExpr]) : List[List[(FExpr, Boolean)]] = {
        val weightmap = patoms.reverse.zipWithIndex.map(a => (a._1, 1 << a._2)).toMap
        val patomsStringPairs = patoms.map(fe => (fe, fe.toString))
        val patomsStringMapReverse = patomsStringPairs.map(p => (p._2, p._1)).toMap

        def missingWeights (cube: List[(FExpr, Boolean)]) = {
            val fexprs = cube.map(_._1)
            val ms = patoms.filter(p => !fexprs.contains(p))
            ms.foldRight(List(0))((e, l) => l.flatMap(mw => List(mw + weightmap(e), mw)))
        }

        val minterms = cnf.flatMap(cube => {
            val mw = missingWeights(cube)
            val cubew = cube.map(lit => if (lit._2) weightmap(lit._1) else 0).sum
            mw.map(_ + cubew)
        })

        qmm.method(minterms, Nil, patomsStringPairs.map(_._2)).map(
            _.map(i => if (i._2) (patomsStringMapReverse(i._1), true) else (patomsStringMapReverse(i._1), false))
        )
    }

    def simplifyConstraint (expr: FExpr) : FExpr = {
        val allAtoms = getAllAtoms(expr)
        val allAtomsPropositions = allAtoms.toList.zipWithIndex.map(a => (a._1, FId(s"prop${a._2}")))
        
        val skelExpr = skeletonizeGeneral(expr, allAtomsPropositions.toMap)
        // Get boolean skeleton from formulae
        val optcnf = getCNF(skelExpr) 
        optcnf match {
            case None => {
                // Sorry, no simplification possible in the general case, yet
                expr
            }
            case Some(cnf) => {
                val simplify1 = elimLiterals(cnf)
                val simplify2 = reduction(simplify1)
                val simplify3 = applyqmm(simplify2, allAtomsPropositions.map(_._2))
                deskeletonizeGeneral(FOpExpr(FOr(), simplify3.map(
                    conj => FOpExpr(FAnd(), conj.map(
                        lit => if (lit._2) lit._1 else FOpExpr(FNot(), List(lit._1))
                    ))
                )), allAtomsPropositions.map(a => (a._2, a._1)).toMap)
            }
        }   
    }
}
