/*
 * SemPat Project.
 * 
 * @file TableauGenerationEngine.scala
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

 * Pattern generation algorithms.
 *
 */

package secant
package tableau

import secant.flang._
import secant.flang.FLang.trueLit

import scala.collection.mutable.Queue
import scala.collection.mutable.MutableList
import scala.collection.immutable


object TableauGenerationEngine {

    def checkValid (platform: MicroPlatform with HasState, secanno: Annotation, t: FlatTableau) : Boolean = {
        secanno match {
            case s: SpeculativeNIAnnotation => t.checkValid(PrePostAnnotation(s.pre, s.post, s.init, s.fin), platform).contains("FAILED")
            case _ => t.checkValid(secanno, platform).contains("FAILED")
        }
    }

    def checkValidSNI (platform: MicroPlatform with HasState with HasSpecFlag, 
        secanno: SpeculativeNIAnnotation, t: FlatTableau, spec: Boolean) : Boolean = {
        t.checkValidSNI(secanno, platform, spec).contains("FAILED")
    }

    def mopPreImage (platform: MicroPlatform with HasState, taintVars: List[FGlobalParam], mop: MicroOp) : Map[FGlobalParam, List[FGlobalParam]] = {
        val taintProp = platform.getAllStages(mop).reverse.foldRight[
            Map[FGlobalParam, List[FStateVar]]](
                (taintVars.map(t => (t, List(t))).toMap)
            )(
                (st, tVmaps) => {
                    tVmaps.map(tVmap => (tVmap._1, 
                        tVmap._2.flatMap(tV => FLangAnalyzer.traceBack(mop.functional(st), tV))
                    )).toMap
                }
            )
        taintProp.map(tVmap =>
            (tVmap._1, tVmap._2.filter(_.isInstanceOf[FGlobalParam]).map(_.asInstanceOf[FGlobalParam]))
        )
        // (taintProp._1.filter(_.isInstanceOf[FGlobalParam]).map(_.asInstanceOf[FGlobalParam]),
        //     taintProp._2.map(pair => (pair._1)))
    }

    def mopInterferes (platform: MicroPlatform with HasState,
        mop: MicroOp, intvars: Set[FGlobalParam]) : Boolean = {
        val taintVars = platform.getAllStages(mop).reverse
            .foldRight[Set[FStateVar]](Set.empty)((st, vars) => {
                vars.++(
                    FLangAnalyzer.modifiesState(mop.functional(st))
                )
            })
        taintVars.filter(_.isInstanceOf[FGlobalParam])
            .map(_.asInstanceOf[FGlobalParam])
            .intersect(intvars).isEmpty
    }

    // Map from types to all variables of that type
    def extractTypes (params: List[FLabeledVar]) : 
        Map[FType, List[FLabeledVar]] = params.groupBy(_.typ)
    
    // Find variables that have the same type
    def filterOrder (fps: (FLabeledVar, FLabeledVar)) : Boolean 
        = (fps._1.toString() < fps._2.toString() && fps._1.lab != fps._2.lab)
    
    def getExprs (params: List[FLabeledVar], 
        filtering: ((FLabeledVar, FLabeledVar)) => Boolean = filterOrder) : List[FExpr] = {
        val typeMap = extractTypes(params)
        typeMap.mapValues(p => (for ( x <- p; y <- p) yield (x, y))
            .toList.filter(filtering(_))
            .map(fps => (fps._1 === fps._2))).values.flatten.toList
    }


    def generateTableau (platform: MicroPlatform with HasState, 
        tgspecs: List[TableauSpecification]) : 
        Map[TableauSpecification, List[AbsTableau]] = {
        
        tgspecs.map(tgspec => (tgspec -> {
            // Extract the annotation from the specification
            val annotation = tgspec match {
                case FlatTableauSpecification(name, facets, anno, grammar) => anno
                case FlowTableauSpecification(name, flows, iflabels, anno, depth, wneg) => anno
                case TreeTableauSpecification(name, flows, iflabels, anno, depth, wneg) => anno
                case TreeTableauSpecificationMultiCon(name, flows, iflabels, anno, depth, wneg) => anno
            }

            // Can taint-based pruning be applied?
            val taintPrune : Boolean = annotation match {
                case a: PrePostAnnotation => true && a.prune
                case s: SpeculationAnnotation => false && s.prune
                case s: SpeculativeNIAnnotation => false && s.prune
            }

            val tableauCandidates : MutableList[FlatTableau] = MutableList.empty
            // Observable variables are Public variables in the postcondition
            val obsVars = annotation.post.filter(_._2 == Public()).map(_._1).toList

            // Generate the grammar (depth is ignored for FlatTableau)
            val grammar = tgspec match {
                case FlatTableauSpecification(name, facets, spec, grammar) => grammar
                case FlowTableauSpecification(name, flows, iflabels, spec, depth, wneg) => 
                    (0 until depth).foldRight[TableauGrammar](TGEps())(
                        (i, gram) => gram match {
                        case a: TGEps => (a >>> platform.getAllMicroOps.toSet)
                        case a: TGChain => (a >>> platform.getAllMicroOps.toSet)
                    })
                case TreeTableauSpecification(name, flows, iflabels, spec, depth, wneg) => 
                    (0 until depth).foldRight[TableauGrammar](TGEps())(
                        (i, gram) => gram match {
                        case a: TGEps => (a >>> platform.getAllMicroOps.toSet)
                        case a: TGChain => (a >>> platform.getAllMicroOps.toSet)
                    })
                case TreeTableauSpecificationMultiCon(name, flows, iflabels, spec, depth, wneg) => 
                    (0 until depth).foldRight[TableauGrammar](TGEps())(
                        (i, gram) => gram match {
                        case a: TGEps => (a >>> platform.getAllMicroOps.toSet)
                        case a: TGChain => (a >>> platform.getAllMicroOps.toSet)
                    })
            }

            SemPatDriver.DEBUG(s"Grammar: ${grammar}")

            // Collection of tableau templates
            val templateQueue = Queue[(FlatTableau, List[FGlobalParam], TableauGrammar)](
                (FlatTableau(List.empty, List.empty, List.empty, List.empty), obsVars, grammar))

            // Expansion phase
            while (!templateQueue.isEmpty) {
                val (tab, tVars, gram) = templateQueue.dequeue()
                var done = false
                if (checkValid(platform, annotation, tab)) {
                    tableauCandidates.+=(tab)
                    SemPatDriver.INFO("Added to candidates: " + tab)
                    // done = true
                }
                if (!taintPrune || !done) { gram match {
                    case TGChain(mops, pre) => { for (mop <- mops) {
                        // Backwards taint propagation
                        val preTVars = mopPreImage(platform, tVars, mop)
                            .map(_._2).flatten.toList.distinct
                        // Get microarchitecturally affected variables
                        val microarchTVars = preTVars.filter(
                            !platform.archState.contains(_)
                        ).toSet
                        // Get microops that interfere with the microarch vars
                        val intmops = platform.getAllMicroOps.filter(
                            mop => mopInterferes(platform, mop, microarchTVars)
                        )
                        SemPatDriver.DEBUG(s"Preimage of ${mop} on ${tVars} is ${preTVars}")
                        
                        // Get the secret inputs
                        val secState = annotation.pre.filter(p => p._2 == Secret())
                            .map(_._1)
                        if (!tVars.toSet.equals(preTVars.toSet) 
                            || secState.exists(preTVars.contains(_)) || !taintPrune) {
                            templateQueue.enqueue((tab.extend(intmops, mop), preTVars, pre))
                        }
                    }}
                    case TGEps() => None
                }}
            }

            SemPatDriver.INFO(s"Templates: ${tableauCandidates.mkString("\n")}")

            // Pruning phase
            if (tableauCandidates.size == 0) {
                SemPatDriver.WARN("No valid tableau templates found")
            }
            tgspec match {
                case tgs: FlatTableauSpecification => 
                    tableauCandidates.map(t => exploreFlatTemplate(platform, t, tgs)).flatten.toList 
                case tgs: FlowTableauSpecification => annotation match {
                    case PrePostAnnotation(_, _, _, _, _) | SpeculationAnnotation(_, _, _, _, _) =>
                        tableauCandidates.map(t => exploreFlowTemplate(platform, t, tgs)).flatten.toList
                    case SpeculativeNIAnnotation(pre, post, init, fin, prune) =>
                        tableauCandidates.map(t => exploreFlowTemplateSNI(platform, t, tgs)).flatten.toList
                }
                case tgs: TreeTableauSpecification => {
                    tableauCandidates.map(t => exploreTreeTemplate(platform, t, tgs)).flatten.toList
                }
                case tgs: TreeTableauSpecificationMultiCon => {
                    tableauCandidates.map(t => exploreTreeTemplateMultiCon(platform, t, tgs)).flatten.toList
                }
            }
        })).toMap
    }

    def exploreFlatTemplate (platform: MicroPlatform with HasState, 
        tableauTemplate: FlatTableau, tgspec: FlatTableauSpecification) : List[FlatTableau] = {
        val annotation = tgspec.spec

        // Get the set of atomic expressions
        val exprs = getExprs(tableauTemplate.tableauSeq
            .flatMap(inode => {
                tgspec.facets.getOrElse(inode._2, List())
                .map(Utils.labelLocalParam(_, inode._1, inode._2))
        }))
        
        SemPatDriver.INFO(s"Exploring template: $tableauTemplate with ${exprs} expressions")

        val allConstraints = MutableList[List[FacetPredicate]]()
        val constraintQ = Queue[(List[FacetPredicate], Int)]((List.empty, 0))
        while (!constraintQ.isEmpty) {
            val (constraint, index) = constraintQ.dequeue()
            if (index < exprs.length) {
                // Branch on an expression try to refine tableau
                val branchOn = exprs(index)
                val poscons = FacetPredicateFlowDef(branchOn)::constraint
                val negcons = FacetPredicateFlowDef(!branchOn)::constraint
                val newTableau1 = tableauTemplate.addFacetPredicates(poscons)
                val newTableau2 = tableauTemplate.addFacetPredicates(negcons)
                val val1 = checkValid(platform, annotation, newTableau1)
                SemPatDriver.DEBUG(s"Tableau ${newTableau1} is ${if (val1) "valid" else "invalid"}")
                val val2 = checkValid(platform, annotation, newTableau2)
                SemPatDriver.DEBUG(s"Tableau ${newTableau2} is ${if (val2) "valid" else "invalid"}")
                if (val1) constraintQ.enqueue((poscons, index+1))
                if (val2) constraintQ.enqueue((negcons, index+1))
                if (!val1 && !val2) allConstraints.+=(constraint)
            } else {
                allConstraints.+=(constraint)
            }
        }
        allConstraints.map(cons => tableauTemplate.addFacetPredicates(cons)).toList
    }

    def exploreFlowTemplate (platform: MicroPlatform with HasState, tableauTemplate: FlatTableau, 
        tgspec: FlowTableauSpecification) : List[FlowTableau] = {
        val annotation = tgspec.spec
        val wneg = tgspec.wneg

        // Find all possible expressions
        val edge_exprs = (tableauTemplate.tableauSeq zip tableauTemplate.tableauSeq.tail)
            .map(pair => {
                val (from, to) = (pair._1._2, pair._2._2)
                // Grab the edges that match the consecutive mops
                val matching_edges = tgspec.edges
                    .filter(flow => flow._1.from == from && flow._1.to == to)
                matching_edges.map(edge => {
                    (edge._1, edge._2(pair._1._1, pair._2._1))
                }).toList
            }).reverse

        val iflabel_exprs = (tableauTemplate.tableauSeq).map(node => {
                // Grab all matching iflabels
                val matching_iflabels = tgspec.iflabels
                    .filter(iflabel => iflabel._1.mop == node._2)
                matching_iflabels.map(iflabel => (iflabel._1, iflabel._2(node._1))).toList
            }).reverse
        SemPatDriver.INFO(s"Exploring template: $tableauTemplate " +
            s"with ${edge_exprs} flow expressions and + ${iflabel_exprs} iflabel expressions")

        // Predicate and hyperexpression constraints
        val allConstraints = MutableList[(List[FacetPredicate], List[FacetPredicateIF])]()
        // Predicate and hyperexpression facets
        val allFacets = MutableList[(List[TableauFlowEdge], List[TableauIFLabel])]()
        
        // Enumerative search queue
        val constraintQ = Queue[(List[FacetPredicate], List[FacetPredicateIF], List[TableauFlowEdge], 
            List[TableauIFLabel], Int, Int)](
                (List.empty, List.empty, List.empty, List.empty, 0, 0))
        while (!constraintQ.isEmpty) {
            val (edge_constraints, iflabel_constraints, edges, iflabels, 
                index, index2) = constraintQ.dequeue()
            if (index < edge_exprs.length) {
                val refinements = edge_exprs(index).map { case (edge, cons) => {
                    val newcons = wneg match {
                        case true => (!cons)::edge_constraints
                        case false => cons::edge_constraints
                    }
                    val tableau = tableauTemplate.addFacetPredicates(newcons)
                    SemPatDriver.DEBUG(s"Checking tableau ${tableau}")
                    val valid = checkValid(platform, annotation, tableau)
                    SemPatDriver.DEBUG(s"Tableau ${tableau} is ${if (valid) "valid" else "invalid"}")
                    
                    if (valid ^ wneg) Some((edge, cons)) else None
                }}.flatten
                if (refinements.isEmpty) {
                    val mop1 = tableauTemplate.tableauSeq(tableauTemplate.tableauSeq.length-index-2)
                    val mop2 = tableauTemplate.tableauSeq(tableauTemplate.tableauSeq.length-index-1)
                    val edge = TableauFlowEdge(mop1._2, mop2._2)
                    constraintQ.enqueue((FacetPredicateFlowDef(trueLit)::edge_constraints, iflabel_constraints, 
                        edge::edges, iflabels, index+1, index2))
                } else refinements.foreach { case (edge, cons) => {
                    SemPatDriver.DEBUG(s"Adding edge ${edge} to flow at index ${index}")
                    constraintQ.enqueue((cons::edge_constraints, iflabel_constraints, 
                        edge::edges, iflabels, index+1, index2))
                }}
            } else if (index2 < iflabel_exprs.length) {
                val iflabel_refs = iflabel_exprs(index2).map { case (iflabel, cons) => {
                    // val predcons = if (edge_constraints.length == 1) edge_constraints.head 
                    //     else FOpExpr(FAnd(), edge_constraints)
                    val posTableau = tableauTemplate.addFacetPredicates(edge_constraints)
                        .addHyperExprs(cons::iflabel_constraints)
                    SemPatDriver.DEBUG(s"Checking tableau ${posTableau}")
                    val posValid = checkValid(platform, annotation, posTableau)
                    SemPatDriver.DEBUG(s"Tableau ${posTableau} is ${if (posValid) "valid" else "invalid"}")
                    
                    if (!posValid) Some((iflabel, cons))
                    else None
                }}.flatten
                if (iflabel_refs.isEmpty) {
                    val mop = tableauTemplate.tableauSeq(tableauTemplate.tableauSeq.length-index-1)
                    constraintQ.enqueue((edge_constraints, FacetPredicateIFDef(trueLit)::iflabel_constraints, 
                        edges, TableauIFLabel(mop._2)::iflabels, index, index2+1))
                } else iflabel_refs.foreach { case (iflabel, cons) => {
                    SemPatDriver.DEBUG(s"Adding iflabel ${iflabel} to flow at index ${index2}")
                    constraintQ.enqueue((edge_constraints, cons::iflabel_constraints, 
                        edges, iflabel::iflabels, index, index2+1))
                }}
            } else {
                allConstraints.+=((edge_constraints, iflabel_constraints))
                allFacets.+=((edges, iflabels))
            }
        }
        SemPatDriver.INFO(s"All constraints: ${allConstraints.toList}")
        SemPatDriver.INFO(s"All flows: ${allFacets.mkString("\n")}")
        (allConstraints zip allFacets).map({ case (cons, facet) => 
            FlowTableau(tableauTemplate.tableauSeq, tableauTemplate.ninterf, 
                cons._1, cons._2, facet._1, facet._2)
        }).toList
    }

    // Add constraints a tree-based predicates
    def exploreTreeTemplate (platform: MicroPlatform with HasState, tableauTemplate: FlatTableau, 
        tgspec: TreeTableauSpecification) : List[TreeTableau] = {
        val annotation = tgspec.spec
        val wneg = tgspec.wneg

        val exprs = tableauTemplate.tableauSeq.dropRight(1).zipWithIndex.map ({
            case (from, i) => tableauTemplate.tableauSeq.drop(i+1).flatMap(
                to => {
                    val flowedges = tgspec.edges.filter(flow => flow._1.from == from._2 && flow._1.to == to._2)
                    flowedges.map(edge => {
                        ((edge._1, from._1, to._1), edge._2(from._1, to._1))
                    }).toList
                }
            )
        })
        
        SemPatDriver.INFO(s"Exploring template: $tableauTemplate with ${exprs} expressions")

        val allConstraints = MutableList[List[FacetPredicate]]()
        val allFacets = MutableList[List[(TableauFlowEdge, Int, Int)]]()
        val constraintQ = Queue[(List[FacetPredicate], List[(TableauFlowEdge, Int, Int)], Int)](
            (List.empty, List(), 0))
        while (!constraintQ.isEmpty) {
            val (constraint, edges, index) = constraintQ.dequeue()
            if (index < exprs.length) {
                val optedges = exprs(index).map {
                    case (edge, cand) => {
                        val branch = wneg match {
                            case false => cand::constraint
                            case true => (!cand)::constraint
                        }
                        val tableau = tableauTemplate.addFacetPredicates(branch)
                        val valid = checkValid(platform, annotation, tableau)
                        SemPatDriver.DEBUG(s"Tableau ${tableau} is ${if (valid) "valid" else "invalid"}")
                        
                        if (valid ^ wneg) Some((cand, edge))
                        else None
                    }
                }.flatten
                if (optedges.isEmpty)  {
                    SemPatDriver.DEBUG(s"Adding default edge to flow at index ${index}")
                    constraintQ.enqueue((FacetPredicateFlowDef(trueLit)::constraint,
                        ((TableauFlowEdge(tableauTemplate.tableauSeq(index)), 
                            tableauTemplate.tableauSeq(index)._1, tableauTemplate.tableauSeq(index)._1))::edges, index+1))
                } else optedges.foreach {
                    case (branch, edge) => {
                        SemPatDriver.DEBUG(s"Adding edge ${edge} to flow at index ${index}")
                        constraintQ.enqueue((branch::constraint, edge::edges, index+1))
                    }
                }
            } else {
                allConstraints.+=(constraint)
                allFacets.+=(edges)
            }
        }
        SemPatDriver.DEBUG(s"All constraints: ${allConstraints.toList}")
        SemPatDriver.INFO(s"All flows: ${allFacets.mkString("\n")}")
        (allConstraints zip allFacets).map({
            case (cons, facet) => TreeTableau(tableauTemplate.tableauSeq, tableauTemplate.ninterf, cons, facet)
        }).toList
    }

    // Add constraints a tree-based predicates
    def exploreTreeTemplateMultiCon (platform: MicroPlatform with HasState, tableauTemplate: FlatTableau, 
        tgspec: TreeTableauSpecificationMultiCon) : List[TreeTableau] = {
        val annotation = tgspec.spec
        val wneg = tgspec.wneg

        val exprs = tableauTemplate.tableauSeq.drop(1).reverse.zipWithIndex.map ({
            case (to_, i) => tableauTemplate.tableauSeq.dropRight(i+1).flatMap(
                from_ => {
                    val flowedges = tgspec.edges.filter(flow => flow._1.from == from_._2 && flow._1.to == to_._2)
                    flowedges.map(edge => {
                        ((edge._1, from_._1, to_._1), edge._2(from_._1, to_._1))
                    }).toList
                }
            )
        })
        
        SemPatDriver.INFO(s"Exploring template: $tableauTemplate with ${exprs} expressions")

        val allConstraints = MutableList[List[FacetPredicate]]()
        val allFacets = MutableList[List[(TableauFlowEdge, Int, Int)]]()
        val constraintQ = Queue[(List[FacetPredicate], List[(TableauFlowEdge, Int, Int)], Int)](
            (List.empty, List.empty, 0))
        while (!constraintQ.isEmpty) {
            val (constraint, edges, index) = constraintQ.dequeue()
            if (index < exprs.length) {
                val optedges = exprs(index).map {
                    // Considers all expressions at a single index
                    case (edge, cand) => {
                        val branch = wneg match {
                            case false => cand::constraint
                            case true => (!cand)::constraint
                        }
                        val tableau = tableauTemplate.addFacetPredicates(branch)

                        SemPatDriver.DEBUG(s"Checking tableau ${tableau}")
                        val valid = checkValid(platform, annotation, tableau)
                        SemPatDriver.DEBUG(s"Tableau ${tableau} is ${if (valid) "valid" else "invalid"}")
                        
                        if (valid ^ wneg) Some((cand, edge))
                        else None
                    }
                }.flatten
                if (optedges.isEmpty)  {
                    val pairwise = (0 until exprs(index).length).map(
                        ind1_ => (0 until ind1_).map((_, ind1_))
                    ).flatten
                    val optedges2 = pairwise.map {
                        case (ind1, ind2) => {
                            val (edge1, cand1) = exprs(index)(ind1)
                            val (edge2, cand2) = exprs(index)(ind2)
                            val branch = wneg match {
                                case false => cand1::cand2::constraint
                                case true => (!cand1)::(!cand2)::constraint
                            }
                            val tableau = tableauTemplate.addFacetPredicates(branch)
                            SemPatDriver.DEBUG(s"Checking tableau ${tableau}")
                            val valid = checkValid(platform, annotation, tableau)
                            SemPatDriver.DEBUG(s"Tableau ${tableau} is ${if (valid) "valid" else "invalid"}")
                            
                            if (valid ^ wneg) List((cand1, edge1), (cand2, edge2))
                            else List.empty
                        }
                    }.flatten
                    // Even considering two counterfactuals at the same time is not enough
                    if (optedges2.isEmpty) {
                        val triplewise = (0 until exprs(index).length).map(
                            ind1_ => (0 until ind1_).map(
                                ind2_ => (0 until ind2_).map((_, ind2_, ind1_))
                            ).flatten
                        ).flatten
                        val optedges3 = triplewise.map {
                            case (ind1, ind2, ind3) => {
                                val (edge1, cand1) = exprs(index)(ind1)
                                val (edge2, cand2) = exprs(index)(ind2)
                                val (edge3, cand3) = exprs(index)(ind3)
                                val branch = wneg match {
                                    case false => cand1::cand2::cand3::constraint
                                    case true => (!cand1)::(!cand2)::(!cand3)::constraint
                                }
                                val tableau = tableauTemplate.addFacetPredicates(branch)
                                SemPatDriver.DEBUG(s"Checking tableau ${tableau}")
                                val valid = checkValid(platform, annotation, tableau)
                                SemPatDriver.DEBUG(s"Tableau ${tableau} is ${if (valid) "valid" else "invalid"}")
                                
                                if (valid ^ wneg) List((cand1, edge1), (cand2, edge2), (cand3, edge3))
                                else List.empty
                            }
                        }.flatten
                        // Even considering three counterfactuals at the same time is not enough
                        // Skip constraints on the this altogether
                        if (optedges3.isEmpty) {
                            SemPatDriver.DEBUG(s"Adding default edge to flow at index ${index}")
                            constraintQ.enqueue((FacetPredicateFlowDef(trueLit)::constraint,
                                ((TableauFlowEdge(tableauTemplate.tableauSeq(index)), 
                                    tableauTemplate.tableauSeq(index)._1, tableauTemplate.tableauSeq(index)._1))::edges, index+1))
                        } else optedges3.foreach {
                            case (branch, edge) => {
                                SemPatDriver.DEBUG(s"Adding edge ${edge} to flow at index ${index}")
                                constraintQ.enqueue((branch::constraint, edge::edges, index+1))
                            }
                        }
                    } else optedges2.foreach {
                        case (branch, edge) => {
                            SemPatDriver.DEBUG(s"Adding edge ${edge} to flow at index ${index}")
                            constraintQ.enqueue((branch::constraint, edge::edges, index+1))
                        }
                    }
                } else optedges.foreach {
                    case (branch, edge) => {
                        SemPatDriver.DEBUG(s"Adding edge ${edge} to flow at index ${index}")
                        constraintQ.enqueue((branch::constraint, edge::edges, index+1))
                    }
                }
            } else {
                allConstraints.+=(constraint)
                allFacets.+=(edges)
            }
        }
        SemPatDriver.DEBUG(s"All constraints: ${allConstraints.toList}")
        SemPatDriver.INFO(s"All flows: ${allFacets.mkString("\n")}")
        (allConstraints zip allFacets).map({
            case (cons, facet) => TreeTableau(tableauTemplate.tableauSeq, tableauTemplate.ninterf, cons, facet)
        }).toList
    }



    def exploreFlowTemplateSNI (platform_ : MicroPlatform with HasState, tableauTemplate: FlatTableau, 
        tgspec: FlowTableauSpecification) : List[FlowTableau] = {
        val annotation = tgspec.spec match {
            case s: PrePostAnnotation => SemPatDriver.ERROR("Cannot use SNI with PrePostAnnotation")
            case s: SpeculationAnnotation => SemPatDriver.ERROR("Cannot use SNI with SpeculationAnnotation")
            case s: SpeculativeNIAnnotation => s
        }
        val platform = platform_ match {
            case p: MicroPlatform with HasState with HasSpecFlag => p
            case _ => SemPatDriver.ERROR("Cannot use SNI without SpecFlag")
        }
        val wneg = tgspec.wneg

        // Find all possible expressions
        val edge_exprs = (tableauTemplate.tableauSeq zip tableauTemplate.tableauSeq.tail)
            .map(pair => {
                val (from, to) = (pair._1._2, pair._2._2)
                // Grab the edges that match the consecutive mops
                val matching_edges = tgspec.edges
                    .filter(flow => flow._1.from == from && flow._1.to == to)
                matching_edges.map(edge => {
                    (edge._1, edge._2(pair._1._1, pair._2._1))
                }).toList
            }).reverse

        val iflabel_exprs = (tableauTemplate.tableauSeq).map(node => {
                // Grab all matching iflabels
                val matching_iflabels = tgspec.iflabels
                    .filter(iflabel => iflabel._1.mop == node._2)
                matching_iflabels.map(iflabel => (iflabel._1, iflabel._2(node._1))).toList
            }).reverse
        SemPatDriver.INFO(s"Exploring template: $tableauTemplate " +
            s"with ${edge_exprs} flow expressions and + ${iflabel_exprs} iflabel expressions")

        // Predicate and hyperexpression constraints
        val allConstraints = MutableList[(List[FacetPredicate], List[FacetPredicateIF])]()
        // Predicate and hyperexpression facets
        val allFacets = MutableList[(List[TableauFlowEdge], List[TableauIFLabel])]()
        
        // Enumerative search queue
        val constraintQ = Queue[(List[FacetPredicate], List[FacetPredicateIF], List[TableauFlowEdge], 
            List[TableauIFLabel], Int, Int)](
                (List.empty, List(), List(), List(), 0, 0))
        while (!constraintQ.isEmpty) {
            val (edge_constraints, iflabel_constraints, edges, iflabels, 
                index, index2) = constraintQ.dequeue()
            if (index < edge_exprs.length) {
                val refinements = edge_exprs(index).map { case (edge, cons) => {
                    val newcons = wneg match {
                        case true => (!cons)::edge_constraints
                        case false => cons::edge_constraints
                    }
                    val tableau = tableauTemplate.addFacetPredicates(newcons)
                    SemPatDriver.DEBUG(s"Checking tableau ${tableau}")
                    val valid = checkValidSNI(platform, annotation, tableau, true)
                    SemPatDriver.DEBUG(s"Tableau ${tableau} with speculation " +
                        s" is ${if (valid) "valid" else "invalid"}")

                    if (valid ^ wneg) Some((edge, cons)) else None
                }}.flatten
                if (refinements.isEmpty) {
                    val mop1 = tableauTemplate.tableauSeq(tableauTemplate.tableauSeq.length-index-2)
                    val mop2 = tableauTemplate.tableauSeq(tableauTemplate.tableauSeq.length-index-1)
                    val edge = TableauFlowEdge(mop1._2, mop2._2)
                    constraintQ.enqueue((FacetPredicateFlowDef(trueLit)::edge_constraints, iflabel_constraints, 
                        edge::edges, iflabels, index+1, index2))
                } else refinements.foreach { case (edge, cons) => {
                    SemPatDriver.DEBUG(s"Adding edge ${edge} to flow at index ${index}")
                    constraintQ.enqueue((cons::edge_constraints, iflabel_constraints, 
                        edge::edges, iflabels, index+1, index2))
                }}
            } else if (index2 < iflabel_exprs.length) {
                val iflabel_refs = iflabel_exprs(index2).map { case (iflabel, cons) => {
                    // val predcons = if (edge_constraints.length == 1) edge_constraints.head 
                    //     else FOpExpr(FAnd(), edge_constraints)
                    val baseTableau = tableauTemplate.addFacetPredicates(edge_constraints)
                    val posTableau = baseTableau.addHyperExprs(cons::iflabel_constraints)
                    SemPatDriver.DEBUG(s"Checking tableau ${posTableau}")
                    
                    val nospecValid = checkValidSNI(platform, annotation, posTableau, false)
                    SemPatDriver.DEBUG(s"Tableau ${posTableau} without speculation " +
                        s" is ${if (nospecValid) "valid" else "invalid"}")
                    if (!nospecValid) {
                        val specValid = checkValidSNI(platform, annotation, posTableau, true)
                        SemPatDriver.DEBUG(s"Tableau ${posTableau} with speculation " +
                            s" is ${if (specValid) "valid" else "invalid"}")
                        if (specValid) {
                            allConstraints.+=((edge_constraints, cons::iflabel_constraints))
                            allFacets.+=((edges, iflabel::iflabels))
                        }
                        None
                    } else {
                        Some ((iflabel, cons))
                    }
                }}.flatten
                if (iflabel_refs.isEmpty) {
                    val mop = tableauTemplate.tableauSeq(tableauTemplate.tableauSeq.length-index-1)
                    constraintQ.enqueue((edge_constraints, FacetPredicateIFDef(trueLit)::iflabel_constraints, 
                        edges, TableauIFLabel(mop._2)::iflabels, index, index2+1))
                } else iflabel_refs.foreach { case (iflabel, cons) => {
                    SemPatDriver.DEBUG(s"Adding iflabel ${iflabel} to flow at index ${index2}")
                    constraintQ.enqueue((edge_constraints, cons::iflabel_constraints, 
                        edges, iflabel::iflabels, index, index2+1))
                }}
            }
        }
        SemPatDriver.INFO(s"All constraints: ${allConstraints.toList}")
        SemPatDriver.INFO(s"All flows: ${allFacets.mkString("\n")}")
        (allConstraints zip allFacets).map({ case (cons, facet) => 
            FlowTableau(tableauTemplate.tableauSeq, tableauTemplate.ninterf, 
                cons._1, cons._2, facet._1, facet._2)
        }).toList
        
    }
}

