/*
 * SemPat Project.
 * 
 * @file FunctionalSolver.scala
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

import uclid.lang._
import uclid.UclidProceduralMain
import Utils.{getCopy, expandLocalParam}


import secant.flang._
import secant.flang.FLang._
import secant.flang.FLangUclidInterface._
import secant.flang.FLangUclidInterface
import secant.MicroProgram.{InstrOperandSymb, InstrOperandValue, RuntimeParam, RuntimePEval}
import secant.tableau.{AbsTableau, FlatTableau}
import virparser.{VIRAtomicBlock, PEvalInfo}

sealed abstract class VarSecAnno
case class Secret() extends VarSecAnno
case class Public() extends VarSecAnno
case class Independent() extends VarSecAnno

sealed abstract class Annotation (val pre: FunctionalSolver.VarSecAnnoMap, val post: FunctionalSolver.VarSecAnnoMap, 
    val init: FExpr = FBoolLit(true), val fin: FExpr = FBoolLit(true), val prune : Boolean = true)
case class PrePostAnnotation (override val pre : FunctionalSolver.VarSecAnnoMap, override val post : FunctionalSolver.VarSecAnnoMap, 
    override val init: FExpr = FBoolLit(true), override val fin: FExpr = FBoolLit(true), override val prune : Boolean = true) extends Annotation(pre, post, init, fin)
case class SpeculationAnnotation (override val pre: FunctionalSolver.VarSecAnnoMap, override val post: FunctionalSolver.VarSecAnnoMap,
    override val init: FExpr = FBoolLit(true), override val fin: FExpr = FBoolLit(true), override val prune : Boolean = true) extends Annotation(pre, post, init, fin)
case class SpeculativeNIAnnotation (override val pre: FunctionalSolver.VarSecAnnoMap, override val post: FunctionalSolver.VarSecAnnoMap,
    override val init: FExpr = FBoolLit(true), override val fin: FExpr = FBoolLit(true), override val prune : Boolean = true) extends Annotation(pre, post, init, fin)

object ComputationModel {
    type EventSequence = List[MicroEvent]
    
    def getStmtFromFunctional (s: FStmt, lab: Int, mop: MicroOp) : FStmt = {
        FLang.rewriteStmt(s, (p: FStateVar) => p match {
            case p: FGlobalParam => FVar(p.id, p.typ)
            case p: FLocalParam => FVar(expandLocalParam(p, lab, mop), p.typ)
            case _ => {
                SemPatDriver.ERROR(s"Unexpected state variable ${p} of class ${p.getClass()} in getStmtForEvent. " +
                    s"All state variables must be FParams before hardening. Aborting...")
                throw new Exception("Unexpected state variable in getStmtForEvent.")
            }
        })
    }

    def getStmtForEvent (ev: MicroEvent, prefarch: Boolean) : FStmt = {
        val basestmt = if (prefarch) ev.mop match {
            case mwarch: MicroOp with HasArchFunctional => mwarch.archfunctional.getOrElse(ev.st, FSkip())
            case _ => ev.mop.functional.getOrElse(ev.st, FSkip())
        } else ev.mop.functional.getOrElse(ev.st, FSkip())
        // if branch, then add an assume over the condition
        val withcond = ev.mop match {
            case mb: BranchOp => block(basestmt, FAssume(mb.condition))
            case _ => basestmt
        }
        getStmtFromFunctional (withcond, ev.lab, ev.mop)
    }

    def stitchIntoSequence (lab: Int, mop: MicroOp, seq: EventSequence, prefarch: Boolean, 
        f: MicroProgram.ParamAnnotationMap) : FStmt = 
        FBlock(seq.map(getStmtForEvent(_, prefarch)) ++ 
            f.map({case (k, v) => v match {
                case RuntimePEval(v, ex) => ex match {
                    case Some(e) => Some(getStmtFromFunctional(FAssume((k === v) || e), lab, mop))
                    case None => Some(getStmtFromFunctional(FAssume((k === v)), lab, mop))
                } 
                case _ => None
            }}).flatten
        )

    def inOrderComputation (mp: MicroPlatform, mprog: LabeledMicroProgram, prefarch : Boolean = false) : FStmt = {
        mprog match {
            case LabeledMicroBranch(lab, cond, thenBranch, elseBranch, f) => {
                val thenStmt = inOrderComputation(mp, thenBranch, prefarch)
                val elseStmt = inOrderComputation(mp, elseBranch, prefarch)
                val stages = mp.getAllStages(cond)
                val condevents = stages.map(s => MicroEvent(lab, cond, s))
                FLang.block(
                    stitchIntoSequence(lab, cond, condevents, prefarch, f),
                    FIfElseStmt(cond match {
                    case mb: BranchOp => mb.condition
                }, thenStmt, elseStmt))
            }
            case LabeledMicroInstr(lab, mop, f) => {
                val stages = mp.getAllStages(mop)
                val events = stages.map(s => MicroEvent(lab, mop, s))
                stitchIntoSequence(lab, mop, events, prefarch, f)
            }
            case LabeledMicroSequence(ops) => {
                FBlock(ops.map(i => inOrderComputation(mp, i, prefarch)))
            }
        }
    }

}


object FunctionalSolver {

    type VarSecAnnoMap = Map[FGlobalParam, VarSecAnno]

    def getEquality (v: FParam) : FExpr = {
        val ind = FId("index_id")
        v match {
            case FGlobalParam(id, typ) => typ match {
                case FArrayType(indexType, elemType) => {
                    elemType match {
                        case FArrayType(indexType1, elemType1) => indexType1 match {
                            case FBoolType() => FForall(ind, indexType,
                                (FVar(getCopy(id, 1), typ)(ind)(trueLit) === FVar(getCopy(id, 2), typ)(ind)(trueLit)) &&
                                (FVar(getCopy(id, 1), typ)(ind)(falseLit) === FVar(getCopy(id, 2), typ)(ind)(falseLit))
                            )
                            case FBitVectorType(width) => FForall(ind, indexType,
                                FOpExpr(FAnd(), (0 to (1 << width)-1).map(i =>
                                    (FVar(getCopy(id, 1), typ)(ind)(bv(i, width)) === 
                                        FVar(getCopy(id, 2), typ)(ind)(bv(i, width)))).toList
                                )
                            )
                            case _ => SemPatDriver.ERROR(s"Unexpected index type ${indexType1} in getEquality. Aborting...")
                        }
                        case _ => FForall(ind, indexType,
                            FVar(getCopy(id, 1), typ)(ind) === FVar(getCopy(id, 2), typ)(ind)
                        )
                    }
                }
                case _ => (FVar(getCopy(id, 1), typ) === FVar(getCopy(id, 2), typ))
            }
            case FLocalParam(id, typ) => typ match {
                case FArrayType(indexType, elemType) => {
                    FForall(ind, indexType,
                        FVar(getCopy(id, 1), typ)(ind) === FVar(getCopy(id, 2), typ)(ind)
                    )
                }
                case _ => (FVar(getCopy(id, 1), typ) === FVar(getCopy(id, 2), typ))
            }
        }
    }

    def getPreAssumes (mp: MicroPlatform with HasState, varanno: VarSecAnnoMap, initanno : FExpr) : List[FExpr] = {
        val hardenedInit = rewriteHardenExpr(initanno)
        mp.stateVars.filter((v: FGlobalParam) => 
            varanno.get(v) match {
                case Some(a) => a == Public()
                case None => false
            }
        ).map((v: FGlobalParam) => getEquality(v)) ++ List(
            Utils.mkHardenedExprCopy(hardenedInit, 1), 
            Utils.mkHardenedExprCopy(hardenedInit, 2)
        )
    }
    def getPostAsserts (mp: MicroPlatform with HasState, varanno: VarSecAnnoMap) : List[FExpr] = {
        mp.stateVars.filter((v: FGlobalParam) => 
            varanno.get(v) match {
                case Some(a) => a == Public()
                case None => false
            }
        ).map((v: FGlobalParam) => getEquality(v))
    }
    
    // Collect all the global state variables, functions, and types
    // These are converted to UCLID declarations
    def collectAllFunctions (mp: MicroPlatform with HasState) : List[Decl] = {
        mp.ufuncs.map((f: FFunc) => f match {
            case FUFunc(id, inp, out) => uclid.lang.FunctionDecl(iden(f.id), 
                FunctionSig(((0 to inp.length).map(a => iden(s"arg$a")) zip inp.map((t: FType) => FtoUclidType(t))).toList, FtoUclidType(out))
            )
            case FDefine(id, args, out, body) => {
                val uidargs = args.map(arg => iden(arg._1.id))
                uclid.lang.DefineDecl(iden(f.id), 
                    FunctionSig(args.map(arg => (iden(arg._1.id), FtoUclidType(arg._2))), FtoUclidType(out)),
                FtoUclidExpr(body(args.map(_._1))))
            }
        })
            
    }
    def collectAllTypes (mp: MicroPlatform with HasState) : List[TypeDecl] = {
        mp.customTypes.map((t: FType) => t match {
            case FUninterpretedType(name) => Some(TypeDecl(iden(name), FtoUclidType(t)))
            case FBoolType() => None
            case FBitVectorType(width) => None
            case FArrayType(indexType, elemType) => None
            case FIntType() => None
        }).flatten
    }

    def getProgEqual (mprog: LabeledMicroProgram) : List[FExpr] = {
        mprog match {
            case LabeledMicroBranch(lab, cond, thenBranch, elseBranch, fields) => cond.parameters.flatMap(
                (p: FLocalParam) => fields(p) match {
                    case InstrOperandValue(_) => Some(getEquality(FLocalParam(expandLocalParam(p, lab, cond), p.typ)))
                    case InstrOperandSymb() => Some(getEquality(FLocalParam(expandLocalParam(p, lab, cond), p.typ)))
                    case _ => None
                }
            ) ++ getProgEqual(thenBranch) ++ getProgEqual(elseBranch)
            case LabeledMicroInstr(lab, mop, fields) => mop.parameters.flatMap(
                (p: FLocalParam) => fields(p) match {
                    case InstrOperandValue(_) => Some(getEquality(FLocalParam(expandLocalParam(p, lab, mop), p.typ)))
                    case InstrOperandSymb() => Some(getEquality(FLocalParam(expandLocalParam(p, lab, mop), p.typ)))
                    case _ => None
                }
            )
            case LabeledMicroSequence(ops) => ops.flatMap((o: LabeledMicroProgram) => getProgEqual(o))
        }
    }

    def collectAllLocalParamDecls (mprog: LabeledMicroProgram, cpy: Int) : List[uclid.lang.Decl] = {
        mprog match {
            case LabeledMicroBranch(lab, cond, thenBranch, elseBranch, fields) => cond.parameters.map(
                (p: FLocalParam) => fields(p) match {
                    // Some specified value: then map it to a constant
                    case InstrOperandValue(v) => ConstantLitDecl(iden(getCopy(expandLocalParam(p, lab, cond), cpy)), FtoUclidNumericLit(v))
                    case InstrOperandSymb() => StateVarsDecl(List(iden(getCopy(expandLocalParam(p, lab, cond), cpy))), FtoUclidType(p.typ))
                    case RuntimeParam() => StateVarsDecl(List(iden(getCopy(expandLocalParam(p, lab, cond), cpy))), FtoUclidType(p.typ))
                    // Unspecified value of the field
                    case RuntimePEval(v, _) => StateVarsDecl(List(iden(getCopy(expandLocalParam(p, lab, cond), cpy))), FtoUclidType(p.typ))
                    case _ => {
                        SemPatDriver.ERROR(s"Unspecified value for local parameter ${p.id} in MicroBranch cond ${cond}. Exiting...")
                        throw new Exception("Unspecified value for local parameter in MicroBranch.")
                    }
                }
            ) ++ collectAllLocalParamDecls(thenBranch, lab) ++ collectAllLocalParamDecls(elseBranch, lab)
            case LabeledMicroInstr(lab, mop, fields) => mop.parameters.map(
                (p: FLocalParam) => fields(p) match {
                    case InstrOperandValue(v) => ConstantLitDecl(iden(getCopy(expandLocalParam(p, lab, mop), cpy)), FtoUclidNumericLit(v))
                    case InstrOperandSymb() => StateVarsDecl(List(iden(getCopy(expandLocalParam(p, lab, mop), cpy))), FtoUclidType(p.typ))
                    case RuntimeParam() => StateVarsDecl(List(iden(getCopy(expandLocalParam(p, lab, mop), cpy))), FtoUclidType(p.typ))
                    // Unspecified value of the field
                    case RuntimePEval(v, _) => StateVarsDecl(List(iden(getCopy(expandLocalParam(p, lab, mop), cpy))), FtoUclidType(p.typ))
                    case _ => {
                        SemPatDriver.ERROR(s"Unspecified value for local parameter ${p.id} in MicroInstr ${LabeledMicroInstr(lab, mop, fields)} mop}. Aborting...")
                        throw new Exception("Unspecified value for local parameter in MicroInstr.")
                    }
                }
            )
            case LabeledMicroSequence(ops) => ops.flatMap((o: LabeledMicroProgram) => collectAllLocalParamDecls(o, cpy))
        }
    }

    def getUclidProgramSingle (mp: MicroPlatform with HasState, mprog: LabeledMicroProgram, exec: FStmt) : List[Decl] = {
        // Collect all the global variable declarations
        val globals1 = mp.stateVars.map((v: FGlobalParam) => StateVarsDecl(List(iden(getCopy(v.id, 1))), FtoUclidType(v.typ)))
        // Collect all the local parameters
        val locals1 = collectAllLocalParamDecls (mprog, 1)

        // Build the execution statement
        val exec1 = Utils.mkHardenedStmtCopy(exec, 1)

        // Create a procedure for microop sequence
        val proc = uclid.lang.ProcedureDecl(
            iden("step"), 
            ProcedureSig(List.empty, List.empty),
            FtoUclidStmt(exec1),
            List(), List(), 
            // Modifies (only set this for the Shared)
            (locals1.map(
                (d: Decl) => d match {
                    case StateVarsDecl(ids, typ) => ids.map(v => ModifiableId(v))
                    case _ => Set.empty
                }).flatten
            ++ globals1.map((d: StateVarsDecl) => d.ids.map(v => ModifiableId(v))).flatten).toSet,
            ProcedureAnnotations(Set.empty))

        collectAllTypes(mp) ++ globals1 ++ locals1 ++ collectAllFunctions(mp) ++ List(proc)
    }

    def getUclidProgramDouble (mp: MicroPlatform with HasState, mprog: LabeledMicroProgram, exec: FStmt) : List[Decl] = {
        // Collect all the global variable declarations
        val globals1 = mp.stateVars.map((v: FGlobalParam) => StateVarsDecl(List(iden(getCopy(v.id, 1))), FtoUclidType(v.typ)))
        val globals2 = mp.stateVars.map((v: FGlobalParam) => StateVarsDecl(List(iden(getCopy(v.id, 2))), FtoUclidType(v.typ)))
        // Collect all the local parameters
        val locals1 = collectAllLocalParamDecls (mprog, 1)
        val locals2 = collectAllLocalParamDecls (mprog, 2)

        // Create a function for microop sequence
        val exec1 = Utils.mkHardenedStmtCopy(exec, 1)
        val exec2 = Utils.mkHardenedStmtCopy(exec, 2)

        // Create a procedure for microop sequence
        val proc = uclid.lang.ProcedureDecl(
            iden("step"), 
            ProcedureSig(List.empty, List.empty),
            FtoUclidStmt(FLang.block(exec1, exec2)),
            List(), List(), 
            // Modifies
            ((locals1 ++ locals2).map(
                (d: Decl) => d match {
                    case StateVarsDecl(ids, typ) => ids.map(v => ModifiableId(v))
                    case _ => Set.empty
                }
            ).flatten ++
                (globals1 ++ globals2).map((d: StateVarsDecl) => d.ids.map(v => ModifiableId(v))).flatten
            ).toSet,
            ProcedureAnnotations(Set.empty))

        collectAllTypes(mp) ++ globals1 ++ globals2 ++ locals1 ++ locals2 ++ collectAllFunctions(mp) ++ List(proc)
    }


    def getTwoSafetyCheck (platform: MicroPlatform with HasState, secanno: Annotation, lmprog: LabeledMicroProgram, 
        assumeDecls: FExpr = FBoolLit(true), hyperAssumeDecls: List[FExpr] = List.empty) : String = {
        secanno match {
            case nianno: PrePostAnnotation => getTwoSafetyCheckNI(platform, nianno, lmprog, assumeDecls, hyperAssumeDecls)
            case speculativeanno : SpeculationAnnotation => {
                platform match {
                    case mp: MicroPlatform with HasSpecFlag => getTwoSafetyCheckSpeculative(mp, speculativeanno, lmprog, assumeDecls)
                    case _ => SemPatDriver.ERROR(s"Speculative annotation ${speculativeanno} on platform ${platform} not supported. Aborting...")
                }
            }
            case snianno: SpeculativeNIAnnotation => {
                platform match {
                    case sp: MicroPlatform with HasSpecFlag => {
                        val ppanno = PrePostAnnotation(snianno.pre, snianno.post, snianno.init, snianno.fin)
                        val wspec = getTwoSafetyCheckNISpeculative(sp, snianno, lmprog, assumeDecls, hyperAssumeDecls, true)
                        val wospec = getTwoSafetyCheckNISpeculative(sp, snianno, lmprog, assumeDecls, hyperAssumeDecls, false)
                        s"With speculation:\n ${wspec}\nWithout speculation:\n ${wospec}"
                    }
                }
            }
        }
    }

    def getTwoSafetyCheckNI (platform: MicroPlatform with HasState, secanno: PrePostAnnotation, 
        lmprog: LabeledMicroProgram, assumeDecls: FExpr, hyperAssumeDecls: List[FExpr]) : String = {
        val preanno = secanno.pre
        val postanno = secanno.post

        // Variable to indicate completion of execution
        val doneVar = StateVarsDecl(List(Identifier("done")), BooleanType())

        // Equality relation on local variables (held initially)
        val localEquality = FunctionalSolver.getProgEqual (lmprog)

        // Initial and next declarations
        val initdecl = InitDecl(BlockStmt(List(), 
            List(AssignStmt(List(LhsId(Identifier("done"))), List(BoolLit(false)))) ++
            FunctionalSolver.getPreAssumes(platform, preanno, secanno.init).map(x => AssumeStmt(FLangUclidInterface.FtoUclidExpr(x), None)) ++
            localEquality.map(x => AssumeStmt(FLangUclidInterface.FtoUclidExpr(x), None))
        ))
        val nextdecl = NextDecl(BlockStmt(List(), List(
                ProcedureCallStmt(Identifier("step"), List(), List(), None, None),
                AssignStmt(List(LhsNextId(Identifier("done"))), List(BoolLit(true)))
            )))

        val assumeDecl1 = AxiomDecl(Some(Identifier("pattern1")), 
            OperatorApplication(ImplicationOp(), List(
                Identifier("done"),
                FLangUclidInterface.FtoUclidExpr(Utils.mkHardenedExprCopy(assumeDecls, 1))
            )), List.empty)
            // FLangUclidInterface.FtoUclidExpr(Utils.mkHardenedExprCopy(assumeDecls, 1)), List.empty)
        val assumeDecl2 = AxiomDecl(Some(Identifier("pattern2")), 
            OperatorApplication(ImplicationOp(), List(
                Identifier("done"),
                FLangUclidInterface.FtoUclidExpr(Utils.mkHardenedExprCopy(assumeDecls, 2))
            )), List.empty)
            // FLangUclidInterface.FtoUclidExpr(Utils.mkHardenedExprCopy(assumeDecls, 2)), List.empty)
        
        val hyperAssumeDecl = AxiomDecl(Some(Identifier("hyperassumes")),
            OperatorApplication(ImplicationOp(), List(
                Identifier("done"), hyperAssumeDecls.length match {
                    case 0 => FtoUclidExpr(FBoolLit(true))
                    case 1 => (FtoUclidExpr(Utils.mkHardenedExprCopy(hyperAssumeDecls(0), 1) === 
                        Utils.mkHardenedExprCopy(hyperAssumeDecls(0), 2)))
                    case _ => OperatorApplication(ConjunctionOp(), hyperAssumeDecls.map(x => 
                        FtoUclidExpr(Utils.mkHardenedExprCopy(x, 1) === Utils.mkHardenedExprCopy(x, 2))
                    ))
                }
            )), List.empty)

        // Get the procedure that acts on the program
        val procdecl = FunctionalSolver.getUclidProgramDouble(platform, lmprog, ComputationModel.inOrderComputation(platform, lmprog))

        // Equivalence which should hold at the end of execution
        val postAsserts = FunctionalSolver.getPostAsserts(platform, postanno)
        val postCondition = Utils.mkHardenedExprCopy(rewriteHardenExpr(secanno.fin), 1) && Utils.mkHardenedExprCopy(rewriteHardenExpr(secanno.fin), 2)

        // Generate commands for unrolling and counterexample printing
        val unroll_cmd = GenericProofCommand(Identifier("unroll"), List.empty, List((IntLit(1), "1")), Some(Identifier("v")), None, None)
        val print_cex_cmd = GenericProofCommand(Identifier("print_cex_json"), List.empty, List.empty, None, Some(Identifier("v")), None)

        // Specification that is checked
        val spec = SpecDecl(Identifier("equiv_final"), OperatorApplication(
                ImplicationOp(), List(
                    Identifier("done"),
                    OperatorApplication(DisjunctionOp(), List(postAsserts.length match {
                        case 0 => FtoUclidExpr(FBoolLit(true))
                        case 1 => FLangUclidInterface.FtoUclidExpr(postAsserts(0))
                        case _ => OperatorApplication(ConjunctionOp(), postAsserts.map(x => FLangUclidInterface.FtoUclidExpr(x)))
                    }, FtoUclidExpr(!postCondition)))
                )), List()
            )

        // println(assumeDecl)
        // Generate config
        val procConfig = UclidProceduralMain.ProceduralConfig("mainProc", List("z3", "-in"), smtFileGeneration = "", "cex", false, true, false, 1)

        SemPatDriver.DEBUG(UclidProceduralMain.getProceduralModuleString(procConfig, procdecl 
            ++ List(doneVar, initdecl, nextdecl)
            ++ List(assumeDecl1, assumeDecl2, hyperAssumeDecl, spec)
        , List(unroll_cmd, print_cex_cmd)))

        // Run the solver
        UclidProceduralMain.solveProcedural(procConfig, procdecl 
                ++ List(doneVar, initdecl, nextdecl)
                ++ List(assumeDecl1, assumeDecl2, hyperAssumeDecl, spec) 
            , List(unroll_cmd, print_cex_cmd))
    }


    def getTwoSafetyCheckSpeculative (platform: MicroPlatform with HasState with HasSpecFlag, secanno: SpeculationAnnotation, lmprog: LabeledMicroProgram, assumeDecls: FExpr) : String = {

        val preanno = secanno.pre
        val postanno = secanno.post

        // Variable to indicate completion of execution
        val doneVar = StateVarsDecl(List(Identifier("done")), BooleanType())

        // Equality relation on local variables (held initially)
        val localEquality = FunctionalSolver.getProgEqual (lmprog)

        // Initial and next declarations
        val initdecl = InitDecl(BlockStmt(List(), 
            List(AssignStmt(List(LhsId(Identifier("done"))), List(BoolLit(false)))) ++
            FunctionalSolver.getPreAssumes(platform, preanno, secanno.init).map(x => AssumeStmt(FLangUclidInterface.FtoUclidExpr(x), None)) ++
            List(FVar(getCopy(platform.spec_on.id, 1), platform.spec_on.typ) === trueLit,
                FVar(getCopy(platform.spec_on.id, 2), platform.spec_on.typ) === falseLit).map(x => AssumeStmt(FLangUclidInterface.FtoUclidExpr(x), None)) ++
            localEquality.map(x => AssumeStmt(FLangUclidInterface.FtoUclidExpr(x), None))
        ))
        val nextdecl = NextDecl(BlockStmt(List(), List(
                ProcedureCallStmt(Identifier("step"), List(), List(), None, None),
                AssignStmt(List(LhsNextId(Identifier("done"))), List(BoolLit(true)))
            )))

        val assumeDecl1 = AxiomDecl(Some(Identifier("pattern1")), 
            OperatorApplication(ImplicationOp(), List(
                Identifier("done"),
                FLangUclidInterface.FtoUclidExpr(Utils.mkHardenedExprCopy(assumeDecls, 1))
            )), List.empty)
            // FLangUclidInterface.FtoUclidExpr(Utils.mkHardenedExprCopy(assumeDecls, 1)), List.empty)
        val assumeDecl2 = AxiomDecl(Some(Identifier("pattern2")), 
            OperatorApplication(ImplicationOp(), List(
                Identifier("done"),
                FLangUclidInterface.FtoUclidExpr(Utils.mkHardenedExprCopy(assumeDecls, 2))
            )), List.empty)
            // FLangUclidInterface.FtoUclidExpr(Utils.mkHardenedExprCopy(assumeDecls, 2)), List.empty)
        
        // Get the procedure that acts on the program
        val procdecl = FunctionalSolver.getUclidProgramDouble(platform, lmprog, ComputationModel.inOrderComputation(platform, lmprog))

        // Equivalence which should hold at the end of execution
        val postAsserts = FunctionalSolver.getPostAsserts(platform, postanno)
        val postCondition = Utils.mkHardenedExprCopy(rewriteHardenExpr(secanno.fin), 1) && Utils.mkHardenedExprCopy(rewriteHardenExpr(secanno.fin), 2)

        // Generate commands for unrolling and counterexample printing
        val unroll_cmd = GenericProofCommand(Identifier("unroll"), List.empty, List((IntLit(1), "1")), Some(Identifier("v")), None, None)
        val print_cex_cmd = GenericProofCommand(Identifier("print_cex_json"), List.empty, List.empty, None, Some(Identifier("v")), None)

        // Specification that is checked
        val spec = SpecDecl(Identifier("equiv_final"), OperatorApplication(
                ImplicationOp(), List(
                    Identifier("done"),
                    OperatorApplication(DisjunctionOp(), List(postAsserts.length match {
                        case 0 => FtoUclidExpr(FBoolLit(true))
                        case 1 => FLangUclidInterface.FtoUclidExpr(postAsserts(0))
                        case _ => OperatorApplication(ConjunctionOp(), postAsserts.map(x => FLangUclidInterface.FtoUclidExpr(x)))
                    }, FtoUclidExpr(!postCondition)))
                )), List()
            )

        // println(assumeDecl)
        // Generate config
        val procConfig = UclidProceduralMain.ProceduralConfig("mainProc", List("z3", "-in"), smtFileGeneration = "", "cex", false, true, false, 1)

        SemPatDriver.DEBUG(UclidProceduralMain.getProceduralModuleString(procConfig, List(doneVar, initdecl, nextdecl) ++ procdecl ++ List(assumeDecl1, assumeDecl2, spec), List(unroll_cmd, print_cex_cmd)))
        // Run the solver
        UclidProceduralMain.solveProcedural(procConfig, procdecl ++ List(doneVar, initdecl, nextdecl) ++ List(assumeDecl1, assumeDecl2, spec), List(unroll_cmd, print_cex_cmd))
    }

    def getTwoSafetyCheckNISpeculative (platform: MicroPlatform with HasState with HasSpecFlag, 
        secanno: SpeculativeNIAnnotation, lmprog: LabeledMicroProgram, assumeDecls: FExpr, 
        hyperAssumeDecls: List[FExpr], spec_on : Boolean) : String = {
        val specassume = spec_on match {
            case true => (FVar(platform.spec_on.id, platform.spec_on.typ) === trueLit)
            case false => (FVar(platform.spec_on.id, platform.spec_on.typ) === falseLit)
        }

        val ppanno = PrePostAnnotation(secanno.pre, secanno.post, secanno.init, secanno.fin)

        getTwoSafetyCheckNI(platform, ppanno, lmprog, assumeDecls && specassume, hyperAssumeDecls)
    }

    /**
      * Simple version of the tableau check for only straight-line programs.
      *
      * @param platform
      * @param secanno
      * @param lmprog
      * @param assumeDecls
      * @param tabl
      * @return
      */
    def getTableauCheck (platform: MicroPlatform with HasState, analyzer: PlatformAnalysisConfig with IsProgramAnalyzer, 
        virab: VIRAtomicBlock, tabl: AbsTableau, pevals: List[Option[PEvalInfo]]) : String = {

        assert(pevals.length == virab.instructions.length, s"PEvalInfo length does not match program length in TableauCheck. Aborting...")

        val lmprog = (virab.instructions zip pevals).map(a => analyzer.vircomp(a._1, a._2))

        def tableauMatchesAt (ilist: List[Int]) : FExpr = {
            val tablIndexToProgIndex = (ilist.zipWithIndex).map(pr => 
                (tabl.tableauSeq(pr._2)._1, lmprog(pr._1).lab)
            ).toMap
            // Only enforce predicate based checks for definite predicates
            Utils.hardenLabeledVarExpr(tabl.getPredicateExpressionsDef(), tablIndexToProgIndex)
        }
        
        // Get all slices of pmopseq that are equal to tmopseq
        val sliceIndices = analyzer.getTableauMatches(virab, pevals, tabl)

        SemPatDriver.DEBUG(s"Tableau matches at ${sliceIndices.length} slices: ${sliceIndices.map(_.mkString(",")).mkString("\n")}")

        // Variable to indicate completion of execution
        val doneVar = StateVarsDecl(List(Identifier("done")), BooleanType())
        // Initial and next declarations
        val initdecl = InitDecl(BlockStmt(List(), 
            // Set done to false
            List(AssignStmt(List(LhsId(Identifier("done"))), List(BoolLit(false))))
        ))
        val nextdecl = NextDecl(BlockStmt(List(), List(
                ProcedureCallStmt(Identifier("step"), List(), List(), None, None),
                AssignStmt(List(LhsNextId(Identifier("done"))), List(BoolLit(true)))
            )))


        
        // Get the procedure that acts on the program
        val procdecl = FunctionalSolver.getUclidProgramSingle(platform, 
            LabeledMicroSequence(lmprog), ComputationModel.inOrderComputation(platform, LabeledMicroSequence(lmprog), true))

        // Generate commands for unrolling and counterexample printing
        val unroll_cmd = GenericProofCommand(Identifier("unroll"), List.empty, List((IntLit(1), "1")), Some(Identifier("v")), None, None)
        val print_cex_cmd = GenericProofCommand(Identifier("print_cex_json"), List.empty, List.empty, None, Some(Identifier("v")), None)

        // A formula saying that none of the instruction slices matched the tableau
        val tableauAbsents = sliceIndices.map(ilist => Utils.mkHardenedExprCopy(!tableauMatchesAt(ilist), 1))
        // Specification that is checked
        val specs = (tableauAbsents zip sliceIndices).map(exprind => 
            SpecDecl(Identifier(s"tableau_absent_${exprind._2.map(lmprog(_).lab).mkString("_")}"), OperatorApplication(
                ImplicationOp(), List(
                    Identifier("done"),
                    FtoUclidExpr(exprind._1)
                )), List())
            )
        
        // Generate config
        val procConfig = UclidProceduralMain.ProceduralConfig("mainProc", List("z3", "-in"), smtFileGeneration = "", "cex", false, true, false, 1)

        SemPatDriver.DEBUG(UclidProceduralMain.getProceduralModuleString(procConfig, List(doneVar, initdecl, nextdecl) ++ procdecl ++ specs, List(unroll_cmd, print_cex_cmd)))
        // Run the solver
        UclidProceduralMain.solveProcedural(procConfig, procdecl ++ List(doneVar, initdecl, nextdecl) ++ specs, List(unroll_cmd, print_cex_cmd))
    }
}