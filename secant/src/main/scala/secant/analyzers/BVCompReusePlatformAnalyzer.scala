package secant

package analyzers

import platforms.BVCompReusePlatform

import secant.flang._
import secant.flang.FLang._
import secant.flang.FLangAnalyzer._

import secant.tableau._
import virparser.{VIRInstruction, VIRAtomicBlock, PEvalInfo, Address, ConcVal, Top}
import virparser.isa.RV32UI
import Utils.llp


class BVCompReusePlatformAnalyzer (platform: BVCompReusePlatform, anconfig: Map[String, Int]) extends PlatformAnalysisConfig with IsProgramAnalyzer {

    import platform._

    val secannotation = PrePostAnnotation (
        pre = Map(regfile -> Public(), fpcount -> Public(), mem -> Secret(), 
            rub_arg1 -> Public(), rub_arg2 -> Public(), rub_valid -> Public()),
        post = Map(fpcount -> Public())
    )

    val opcodeMapping : Map[String, MicroOp] = Map(
        IntALUOp -> List("addi", "slli", "slti", "sltiu", "xori", "srli", "srai", "ori", "andi", "add", "sub", "subw", "sll", "slt", "sltu", "xor", "srl", "sra", "or", "and", "addiw", "slliw", "srliw", "sraiw", "sraw"),
        FPALUOp -> List("mulw", "mul"),
        LoadOp -> List("lw", "lb", "lh", "lbu", "lhu", "ld", "lwu", "lui"),
        StoreOp -> List("sw", "sb", "sh", "sd")
    ).flatMap(pair => pair._2.map(mop => (mop, pair._1)))


    def setOperandValue (flp: FLocalParam, v: Int) : FNLit = {
        flp match {
            case FPALUOp.rs1 | IntALUOp.rs1 | LoadOp.rs1 | StoreOp.rs1 => bv(v, 5)
            case FPALUOp.rs2 | IntALUOp.rs2 | StoreOp.rs2 => bv(v, 5)
            case FPALUOp.rd | IntALUOp.rd | LoadOp.rd => bv(v, 5)
            // TODO: might lead to an issue if the immediate is negative (UCLID bitvecs are unsigned?)
            case LoadOp.imm | StoreOp.imm => bv(if (v >= 0) v else ((1 << 12)+v), platform.ww)
            case _ => SemPatDriver.ERROR(s"Unknown operand ${flp} in VIR instruction. Replacing with 0.")
        }
    }


    // Define the VIR to RISCV compiler here
    def vircomp (viri: VIRInstruction, peval: Option[PEvalInfo]) : LabeledMicroInstr = {
        val (inst, fmap) = RV32UI.parseInst(viri)
        opcodeMapping.get(viri.opcode.opcode) match {
            case None => {
                SemPatDriver.WARN(s"No RISCV opcode for VIR instruction: ${viri.opcode.opcode}. Replacing with NOP.")
                LabeledMicroInstr(viri.loc.loc, NOP)
            }
            case Some(value) => {
                LabeledMicroInstr(viri.loc.loc, value, MicroProgram.mkParamMap(value.parameters.flatMap(param => {
                    fmap.get(param.id) match {
                        case None => Some(param -> MicroProgram.runtimep())
                        case Some(value) => Some(param -> MicroProgram.instopv(setOperandValue(param, value)))
                    }
                    // operandMapping.get(param) match {
                    //     case None => None
                    //     case Some(value) => Some()
                    // }
                })))
            }
        }
    }
    
    /**
      * Matcher that returns dependency filtered matches of Tableau template in the VIRAtomicBlock.
      */
    def matcher1 (virab: VIRAtomicBlock, tabl: AbsTableau) : List[List[Int]] = {
        
        val rtmopseq = tabl.tableauSeq.map(_._2).reverse
        val rtinfseq = tabl.ninterf
        val pmopseq = virab.instructions.map(vircomp(_, None).mop)
        
        val iseqs = pmopseq.zipWithIndex.filter(p => rtmopseq(0) == p._1).map(p => List(p._2))
        rtmopseq.drop(1).foldLeft(iseqs)(
            (acc, mop) => {
                acc.flatMap(
                    iseq => {
                        RV32UI.traceBack(iseq.head, virab).filter(i => mop == pmopseq(i)).map(i => i :: iseq)
                    }
                )
            }
        )
    }

    /**
      * Matcher that returns all regular expression matches
      */
    def matcher2 (virab: VIRAtomicBlock, tabl: FlowTableau, pevals: List[Option[PEvalInfo]]) : List[List[Int]] = {
        
        assert (virab.instructions.length == pevals.length, "Matcher2: VIRAtomicBlock and PEvalInfo list length mismatch.")

        def isIFPredicateSatisfied (peval: Option[PEvalInfo], 
            mip: ((MicroOp, List[MicroOp]), (FacetPredicate, FacetPredicateIF))) : Boolean = {
            peval match {
                case None => true
                case Some(value) => mip._1._1 match {
                    case LoadOp => mip._2._2 match {
                        case FacetPredicateIFHighResult(ex) => value.res match {
                            case Address(a, b) => b
                            case ConcVal(v, b) => false
                            case Top(b) => b
                        }
                        case _ => true
                    }
                    case FPALUOp => mip._2._2 match {
                        case FacetPredicateIFHighOps(ex) => {
                            (value.arg1 match {
                            case Address(a, b) => b
                            case ConcVal(v, b) => false
                            case Top(b) => b
                            }) || (value.arg2 match {
                                case Address(a, b) => b
                                case ConcVal(v, b) => false
                                case Top(b) => b
                            })
                        }
                        case _ => true
                    }
                    case _ => true
                }
            }
        }

        val rtmopseq = tabl.tableauSeq.map(_._2).reverse
        val rtinfseq = tabl.ninterf.reverse
        val predicates = tabl.predicates.reverse
        val ifpredicates = tabl.hyperexprs.reverse
        val pmopseq = virab.instructions.map(vircomp(_, None).mop)
        
        val iseqs = pmopseq.zipWithIndex
            .filter(p => rtmopseq(0) == p._1)
            .filter(p => isIFPredicateSatisfied(pevals(p._2), 
                ((p._1, List()), (predicates(0), ifpredicates(0)))))
            .map(p => List(p._2))

        val matches = (rtmopseq.drop(1) zip rtinfseq zip (predicates zip ifpredicates.drop(1))).foldLeft(iseqs)((acc, mop_infmops_pred) => {
            acc.flatMap(iseq => {
                (mop_infmops_pred._2._1 match {
                    case FacetPredicateAddrDep(ex, _) => RV32UI.traceBack(iseq.head, virab)
                    case FacetPredicateDataDep(ex, _) => RV32UI.traceBack(iseq.head, virab)
                    case FacetPredicateFlowDef(ex) => (0 until iseq.head)
                    case FacetPredicateDiffAddr(_, _) | FacetPredicateSameAddr(_, _) => SemPatDriver.ERROR(s"Matcher2: FacetPredicate ${mop_infmops_pred._2} not supported in flow edges!")
                    case _: FacetPredicateIF => SemPatDriver.ERROR("IF labels for edges not supported in matcher2.")
                }).filter(i => {
                    mop_infmops_pred._1._1 == pmopseq(i)
                }).filter(i => {
                    (i+1 until iseq.head)
                        .forall(j => mop_infmops_pred._1._2.contains(pmopseq(j)))
                }).filter(i => {
                    isIFPredicateSatisfied(pevals(i), mop_infmops_pred)
                }).map(i => {
                    i :: iseq
                })
            })
        })
        SemPatDriver.DEBUG(s"Matches: ${matches}")
        matches
    }

    override def getTableauMatches (virab: VIRAtomicBlock, pevals: List[Option[PEvalInfo]], tabl: AbsTableau) : List[List[Int]] = 
        if (anconfig.getOrElse("matcher", 1) == 1) matcher1 (virab, tabl) 
        else { tabl match {
            case t: FlowTableau => matcher2 (virab, t, pevals)
            case _ => SemPatDriver.ERROR("Matcher 2 only accepts flow tableau.")
        }}

    val tabdepth = anconfig.getOrElse("tabdepth", 3)

    override val tableaus = List(
        tabdepth match {
            case 2 => FlowTableau(
                List((1, LoadOp), (0, FPALUOp)), (0 until 1).map(_ => List(IntALUOp, LoadOp, StoreOp, NOP)).toList,
                List(FacetPredicateDataDep(llp(LoadOp.data, 1, LoadOp) === llp(FPALUOp.op1, 0, FPALUOp)
                    || (llp(LoadOp.data, 1, LoadOp) === llp(FPALUOp.op2, 0, FPALUOp)))),
                List.empty,
                List.empty,
                List.empty
            )
            case 3 => FlowTableau(
                List((2, FPALUOp), (1, LoadOp), (0, FPALUOp)), (0 until 2).map(_ => List(IntALUOp, LoadOp, StoreOp, NOP)).toList,
                List(
                    FacetPredicateFlowDef(trueLit),
                    FacetPredicateDataDep(llp(LoadOp.rd, 1, LoadOp) === llp(FPALUOp.rs1, 0, FPALUOp)
                    || (llp(LoadOp.rd, 1, LoadOp) === llp(FPALUOp.rs2, 0, FPALUOp)))
                ), 
                List(
                    FacetPredicateIFDef(trueLit),
                    FacetPredicateIFDef(trueLit),
                    FacetPredicateIFDef(trueLit)
                ),
                List.empty,
                List.empty
            )
            case _: Int => SemPatDriver.ERROR(s"BVCompReusePlatformAnalyzer: Unsupportted tableau depth ${tabdepth}.")
        }
        
    )
}

object BVCompReusePlatformAnalyzer {
    def apply(platform: MicroPlatform, anconfig: Map[String, Int] = Map.empty) = {
        platform match {
            case p: BVCompReusePlatform => new BVCompReusePlatformAnalyzer(p, anconfig)
            case _ => SemPatDriver.ERROR("BVCompReusePlatformAnalyzerF: Unknown platform type.")
        }
    }
}

class BVCompReuseTableauGenerator (platform: BVCompReusePlatform, genconf: Map[String, Int]) 
    extends PlatformAnalysisConfig with IsTableauGenerator {

    import platform._

    val depth = genconf.getOrElse("depth", 3)

    val flow_atoms : Map[TableauFlowEdge, (Int, Int) => FacetPredicate] = Map(
        // Address dependencies
        TableauFlowEdge("addr_dep", LoadOp, LoadOp) -> ((i, j) => FacetPredicateAddrDep(
            Utils.llp(LoadOp.rd, i, LoadOp) === Utils.llp(LoadOp.rs1, j, LoadOp)
        )),
        TableauFlowEdge("addr_dep", IntALUOp, LoadOp) -> ((i, j) => FacetPredicateAddrDep(
            Utils.llp(IntALUOp.rd, i, IntALUOp) === Utils.llp(LoadOp.rs1, j, LoadOp)
        )),
        // Addr independency
        TableauFlowEdge("addr_indep", LoadOp, LoadOp) -> ((i, j) => FacetPredicateAddrDep(
            Utils.llp(LoadOp.addr, i, LoadOp) !== Utils.llp(LoadOp.addr, j, LoadOp)
        )),
        TableauFlowEdge("addr_indep", IntALUOp, LoadOp) -> ((i, j) => FacetPredicateAddrDep(
            Utils.llp(IntALUOp.rd, i, IntALUOp) !== Utils.llp(LoadOp.rs1, j, LoadOp)
        )),
        // Data dependencies
        TableauFlowEdge("data_dep", LoadOp, IntALUOp) -> ((i, j) => FacetPredicateDataDep(
            Utils.llp(LoadOp.rd, i, LoadOp) === Utils.llp(IntALUOp.rs1, j, IntALUOp)
            || Utils.llp(LoadOp.rd, i, LoadOp) === Utils.llp(IntALUOp.rs2, j, IntALUOp)
        )),
        TableauFlowEdge("data_dep", LoadOp, FPALUOp) -> ((i, j) => FacetPredicateDataDep(
            Utils.llp(LoadOp.rd, i, LoadOp) === Utils.llp(FPALUOp.rs1, j, FPALUOp) 
            || Utils.llp(LoadOp.rd, i, LoadOp) === Utils.llp(FPALUOp.rs2, j, FPALUOp)
        )),
        TableauFlowEdge("data_dep", IntALUOp, IntALUOp) -> ((i, j) => FacetPredicateDataDep(
            Utils.llp(IntALUOp.rd, i, IntALUOp) === Utils.llp(IntALUOp.rs1, j, IntALUOp) 
            || Utils.llp(IntALUOp.rd, i, IntALUOp) === Utils.llp(IntALUOp.rs2, j, IntALUOp)
        )),
        TableauFlowEdge("data_dep", FPALUOp, FPALUOp) -> ((i, j) => FacetPredicateDataDep(
            Utils.llp(FPALUOp.rd, i, FPALUOp) === Utils.llp(FPALUOp.rs1, j, FPALUOp) 
            || Utils.llp(FPALUOp.rd, i, FPALUOp) === Utils.llp(FPALUOp.rs2, j, FPALUOp)
        )),
        TableauFlowEdge("data_dep", IntALUOp, IntALUOp) -> ((i, j) => FacetPredicateDataDep(
            Utils.llp(IntALUOp.rd, i, IntALUOp) === Utils.llp(IntALUOp.rs1, j, IntALUOp) 
            || Utils.llp(IntALUOp.rd, i, IntALUOp) === Utils.llp(IntALUOp.rs2, j, IntALUOp)
        ))
    )

    val archiflab_atoms : Map[TableauIFLabel, (Int) => FacetPredicateIF] = Map(
        TableauIFLabel("sec_input", LoadOp) -> ((i) => 
            FacetPredicateIFHighResult(Utils.llp(LoadOp.data, i, LoadOp))
        )
    )

    val secannotation = PrePostAnnotation (
        pre = Map(regfile -> Public(), fpcount -> Public(), mem -> Secret(),
            rub_arg1 -> Public(), rub_arg2 -> Public(), rub_valid -> Public()),
        post = Map(fpcount -> Public()),
        init = (0 until platform.rubc_size).foldRight[FExpr](trueLit)((i, fe) => (fe && (rub_valid(bv(i, platform.rubc_ptr_width)) === falseLit)))
    )

    val spec_type = genconf.getOrElse("spec_type", 0)

    val tgconfig = List(
        if (spec_type == 0)
            FlowTableauSpecification("flow_new", 
                edges = flow_atoms, iflabels = archiflab_atoms, 
                spec = secannotation, depth = depth, wneg = true
            )
        else
            TreeTableauSpecificationMultiCon("treetableaumulticon", 
                edges = flow_atoms, iflabels = Map.empty,
                spec = secannotation, depth = depth, wneg = true
            )
    )
}

object BVCompReuseTableauGenerator {
    def apply(platform: MicroPlatform, genconf: Map[String, Int] = Map.empty) = {
        platform match {
            case p: BVCompReusePlatform => new BVCompReuseTableauGenerator(p, genconf)
            case _ => SemPatDriver.ERROR("BVCompReuseTableauGeneratorF: Unknown platform type.")
        }
    }
}
