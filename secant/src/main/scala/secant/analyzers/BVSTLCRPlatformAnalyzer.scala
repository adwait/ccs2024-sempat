package secant

package analyzers

import platforms.BVSTLCRPlatform

import flang.FLang._
import flang._
import secant.tableau._
import virparser.{VIRInstruction, VIRAtomicBlock, PEvalInfo, ConcVal, Top, Address}
import virparser.isa.RV32UI


class BVSTLCRPlatformTableauGenerator (platform: BVSTLCRPlatform, genconf: Map[String, Int]) 
    extends PlatformAnalysisConfig with IsTableauGenerator
{
    import platform._

    val depth = genconf.getOrElse("depth", 3)

    val flow_atoms: Map[TableauFlowEdge, (Int, Int) => FacetPredicate] = Map(
        // Data dependency 
        TableauFlowEdge("data_dep1", LoadOp, FPALUOp) -> ((i, j) => FacetPredicateDataDep(
            (Utils.llp(LoadOp.rd, i, LoadOp) === Utils.llp(FPALUOp.rs1, j, FPALUOp))

        )),
        TableauFlowEdge("data_dep2", LoadOp, FPALUOp) -> ((i, j) => FacetPredicateDataDep(
            (Utils.llp(LoadOp.rd, i, LoadOp) === Utils.llp(FPALUOp.rs2, j, FPALUOp))
        )), 
        // Address dependencies
        TableauFlowEdge("addr_dep", LoadOp, LoadOp) -> ((i, j) => FacetPredicateAddrDep(
            Utils.llp(LoadOp.rd, i, LoadOp) === Utils.llp(LoadOp.rs1, j, LoadOp)
        )),
        // Addr independency
        TableauFlowEdge("addr_indep", LoadOp, LoadOp) -> ((i, j) => FacetPredicateAddrDep(
            Utils.llp(LoadOp.rd, i, LoadOp) !== Utils.llp(LoadOp.rs1, j, LoadOp)
        )),
        // Same address
        TableauFlowEdge("same_address", StoreOp, LoadOp) -> ((i, j) => FacetPredicateSameAddr(
            Utils.llp(StoreOp.addr, i, StoreOp) === Utils.llp(LoadOp.addr, j, LoadOp)
        )),
        // Different address
        TableauFlowEdge("diff_address", StoreOp, StoreOp) -> ((i, j) => FacetPredicateDiffAddr(
            Utils.llp(StoreOp.addr, i, StoreOp) !== Utils.llp(StoreOp.addr, j, StoreOp)
        )),
        TableauFlowEdge("diff_address", StoreOp, LoadOp) -> ((i, j) => FacetPredicateDiffAddr(
            Utils.llp(StoreOp.addr, i, StoreOp) !== Utils.llp(LoadOp.addr, j, LoadOp)
        ))   
    )

    val secannotation = SpeculativeNIAnnotation (
        pre = Map(regfile -> Secret(), mem -> Public(), sbuffer_data -> Public(), sbuffer_tags -> Public(), sbuffer_valid -> Public(), 
            // cache_data -> Public(), cache_tags -> Public(), cache_valid -> Public(), 
            rub_arg1 -> Public(), rub_arg2 -> Public(), rub_res -> Public(), rub_valid -> Public(), fpcount -> Public()
        ),
        post = Map(
            // cache_tags -> Public()
            fpcount -> Public()
        ),
        init = ((sbuffer_valid === falseLit) && (store_stalled === falseLit))
    )

    val archiflab_atoms : Map[TableauIFLabel, (Int) => FacetPredicateIF] = Map(
        // TableauIFLabel("true_data", LoadOp) -> ((i) => Utils.llp(LoadOp.true_data, i, LoadOp)),
        TableauIFLabel("sec_addr", LoadOp) -> ((i) => 
            FacetPredicateIFHighAddr(Utils.llp(LoadOp.addr, i, LoadOp))),
        TableauIFLabel("sec_data", StoreOp) -> ((i) => 
            FacetPredicateIFHighOps(Utils.llp(StoreOp.data, i, StoreOp))),
        TableauIFLabel("sec_op1", FPALUOp) -> ((i) => 
            FacetPredicateIFHighOps(Utils.llp(FPALUOp.op1, i, FPALUOp))),
        TableauIFLabel("sec_op2", FPALUOp) -> ((i) => 
            FacetPredicateIFHighOps(Utils.llp(FPALUOp.op2, i, FPALUOp))),
        // TableauIFLabel("sec_input", IntALUOp) -> ((i) => Utils.llp(IntALUOp.op1, i, IntALUOp)),
        // TableauIFLabel("sec_input", FPALUOp) -> ((i) => Utils.llp(FPALUOp.op1, i, FPALUOp))
    )

    val tgconfig: List[TableauSpecification] = List(
        FlowTableauSpecification("stlcr1flow",
            edges = flow_atoms, iflabels = archiflab_atoms, 
            spec = secannotation, depth = depth, wneg = false
        )
    )

}

object BVSTLCRPlatformTableauGenerator {
    def apply (platform: MicroPlatform, genconf: Map[String, Int]) : BVSTLCRPlatformTableauGenerator = {
        platform match {
            case p: BVSTLCRPlatform => new BVSTLCRPlatformTableauGenerator(p, genconf)
            case _ => throw new Exception("Platform not supported")
        }
    }
}


class BVSTLCRPlatformAnalyzer (platform: BVSTLCRPlatform, anconfig: Map[String, Int]) extends PlatformAnalysisConfig with IsProgramAnalyzer {

    import platform._


    val secannotation = SpeculativeNIAnnotation (
        pre = Map(regfile -> Secret(), mem -> Public(), sbuffer_data -> Public(), sbuffer_tags -> Public(), sbuffer_valid -> Public(), 
            // cache_data -> Public(), cache_tags -> Public(), cache_valid -> Public(), 
            rub_arg1 -> Public(), rub_arg2 -> Public(), rub_res -> Public(), rub_valid -> Public(), fpcount -> Public()
        ),
        post = Map(
            // cache_tags -> Public()
            fpcount -> Public()
        ),
        // init = ((sbuffer_valid === falseLit) && (store_stalled === falseLit))
    )


    val opcodeMapping : Map[String, MicroOp] = Map(
        ALUIOp -> List("addi", "slli", "slti", "sltiu", "xori", "srli", "srai", "ori", "andi"),
        ALUROp -> List("add", "sub", 
            "subw", "sll", "slt", "sltu", "xor", "srl", "sra", "or", "and", "addiw", "slliw", "srliw", "sraiw", "sraw"),
        // BOp -> List("beq", "bne", "blt"),
        FPALUOp -> List("mulw", "mul"),
        LoadOp -> List("lw", "lb", "lh", "lbu", "lhu", "ld", "lwu", "lui"),
        StoreOp -> List("sw", "sb", "sh", "sd")
    ).flatMap(pair => pair._2.map(mop => (mop, pair._1)))


    def setOperandValue (flp: FLocalParam, v: Int) : FNLit = {
        flp match {
            case FPALUOp.rs1 | ALUIOp.rs1 | ALUROp.rs2 | LoadOp.rs1 | StoreOp.rs1 => bv(v, 5)
            case FPALUOp.rs2 | ALUROp.rs2 | StoreOp.rs2 => bv(v, 5)
            case FPALUOp.rd | ALUIOp.rd | ALUROp.rd | LoadOp.rd => bv(v, 5)
            // TODO: might lead to an issue if the immediate is negative (UCLID bitvecs are unsigned?)
            case LoadOp.imm | StoreOp.imm | ALUIOp.imm => bv(if (v >= 0) v else ((1 << 12)+v), platform.ww)
            // case BOp.funct3 => bv(v, 3)
            case _ => SemPatDriver.ERROR(s"Unknown operand ${flp} in VIR instruction. Replacing with 0.")
        }
    }


    // Define the VIR to RISCV compiler here
    def vircomp (viri: VIRInstruction, peval: Option[PEvalInfo]) : LabeledMicroInstr = {

        def grabUpdVal (mop: MicroOp, pevals: Option[PEvalInfo]) : Option[(FLocalParam, MicroProgram.ParamAnnotation)] = {
            mop match {
                case LoadOp => peval match {
                    case None => None
                    case Some(p) => p.res match {
                        case ConcVal(v, b) => Some((LoadOp.data, MicroProgram.runtimepeval(bv(v, platform.ww), is_spec)))
                        case _ => None
                    }
                }
                case ALUIOp => peval match {
                    case None => None
                    case Some(p) => p.res match {
                        case ConcVal(v, b) => Some((ALUIOp.res, MicroProgram.runtimepeval(bv(v, platform.ww), is_spec)))
                        case _ => None
                    }
                }
                case ALUROp => peval match {
                    case None => None
                    case Some(p) => p.res match {
                        case ConcVal(v, b) => Some((ALUROp.res, MicroProgram.runtimepeval(bv(v, platform.ww), is_spec)))
                        case _ => None
                    }
                }
                case _ => None
            }
        }

        val (inst, fmap) = RV32UI.parseInst(viri)
        opcodeMapping.get(viri.opcode.opcode) match {
            case None => {
                SemPatDriver.WARN(s"No RISCV opcode for VIR instruction: ${viri.opcode.opcode}. Replacing with NOP.")
                LabeledMicroInstr(viri.loc.loc, NOP)
            }
            case Some(value) => {   
                val parammap = value.parameters.flatMap(param => {
                    fmap.get(param.id) match {
                        case None => Some(param -> MicroProgram.runtimep())
                        case Some(value) => Some(param -> MicroProgram.instopv(setOperandValue(param, value)))
                    }
                }) ++ List(grabUpdVal(value, peval)).flatten
                LabeledMicroInstr(viri.loc.loc, value, MicroProgram.mkParamMap(parammap))
            }
        }
    }
    
    // /**
    //   * Matcher that returns all regular expression matches
    //   */
    def matcher (virab: VIRAtomicBlock, tabl: FlowTableau, pevals: List[Option[PEvalInfo]]) : List[List[Int]] = {
        
        assert (virab.instructions.length == pevals.length, "Matcher2: VIRAtomicBlock and PEvalInfo list length mismatch.")

        def isIFPredicateSatisfied (peval: Option[PEvalInfo], 
            mip: ((MicroOp, List[MicroOp]), (FacetPredicate, FacetPredicateIF))) : Boolean = {
            // print(s"Checking ${mip._1._1} with ${peval} for ${mip._2._2}")
            true
            // println(s" -> ${res}")
        }

        val rtmopseq = tabl.tableauSeq.map(_._2).reverse
        val rtinfseq = tabl.ninterf
        val predicates = tabl.predicates.reverse
        val ifpredicates = tabl.hyperexprs.reverse
        val pmopseq = virab.instructions.map(vircomp(_, None).mop)
        
        val iseqs = pmopseq.zipWithIndex
            .filter(p => rtmopseq(0) == p._1)
            .filter(p => isIFPredicateSatisfied(pevals(p._2), 
                ((p._1, List()), (predicates(0), ifpredicates(0)))))
            .map(p => List(p._2))
        
        val matches = ((rtmopseq.drop(1) zip rtinfseq) zip (predicates zip ifpredicates.drop(1))).foldLeft(iseqs)((acc, mop_infmops_pred) => {
            acc.flatMap(iseq => {
                (mop_infmops_pred._2._1 match {
                    case FacetPredicateAddrDep(ex, _) => RV32UI.traceBack(iseq.head, virab)
                    case FacetPredicateDataDep(ex, _) => RV32UI.traceBack(iseq.head, virab)
                    case FacetPredicateFlowDef(ex) => (0 until iseq.head)
                    case FacetPredicateSameAddr(ex, _) => pevals(iseq.head) match {
                        case None => (0 until iseq.head)
                        case Some(value) => (0 until iseq.head).filter(
                            i => pevals(i) match {
                                case None => true
                                case Some(v) => v.addr match {
                                    case Address(v, b) => value.addr match {
                                        case Address(a, b) => a == v
                                        case _ => true
                                    }
                                    case _ => true
                                }
                            }
                        )
                    }
                    case FacetPredicateDiffAddr(ex, _) => SemPatDriver.ERROR(s"Matcher2: FacetPredicate ${mop_infmops_pred._2._1} not supported in flow edges!")
                    case a: FacetPredicateIF => SemPatDriver.ERROR(s"Matcher2: FacetPredicate ${a} not supported in flow edges!")
                }).filter(i => {
                    mop_infmops_pred._1._1 == pmopseq(i)
                }).filter(i => (i+1 until iseq.head)
                    .forall(j => mop_infmops_pred._1._2.contains(pmopseq(j)))
                ).filter(i => {
                    isIFPredicateSatisfied(pevals(i), mop_infmops_pred)
                }).map(i => i :: iseq)
            })
        })
        SemPatDriver.DEBUG(s"Matches: ${matches}")
        matches
    }

    override def getTableauMatches (virab: VIRAtomicBlock, pevals: List[Option[PEvalInfo]], tabl: AbsTableau) : List[List[Int]] = 
        tabl match {
            case t: FlowTableau => matcher (virab, t, pevals)
            case _ => SemPatDriver.ERROR("Matcher only accepts flow tableau.")
        }

    override val tableaus = List(
        FlowTableau(List((2, StoreOp), (1, LoadOp), (0, FPALUOp)), 
        List(List(ALUIOp, ALUROp, LoadOp, StoreOp, FPALUOp, NOP), List(ALUIOp, ALUROp, LoadOp, StoreOp, FPALUOp, NOP)), 
            List(
                FacetPredicateSameAddr(Utils.llp(StoreOp.addr, 2, StoreOp) === Utils.llp(LoadOp.addr, 1, LoadOp)
                    , Some(Utils.llp(StoreOp.addr, 2, StoreOp) === Utils.llp(LoadOp.addr, 1, LoadOp))
                    ), 
                FacetPredicateDataDep(
                    (Utils.llp(LoadOp.rd, 1, LoadOp) === Utils.llp(FPALUOp.rs1, 0, FPALUOp)) 
                        || (Utils.llp(LoadOp.rd, 1, LoadOp) === Utils.llp(FPALUOp.rs2, 0, FPALUOp))
                )
            ),
            List(
                FacetPredicateIFDef(trueLit),
                FacetPredicateIFDef(trueLit),
                FacetPredicateIFHighOps(trueLit)
            ), List(TableauFlowEdge("same_address", StoreOp, LoadOp), TableauFlowEdge("data_dep", LoadOp, FPALUOp)),
            List()
        )
    )
}

object BVSTLCRPlatformAnalyzer {
    def apply(platform: MicroPlatform, anconfig: Map[String, Int] = Map.empty) = {
        platform match {
            case p: BVSTLCRPlatform => new BVSTLCRPlatformAnalyzer(p, anconfig)
            case _ => SemPatDriver.ERROR("BVSTLCRPlatformAnalyzer: Unknown platform type.")
        }
    }
}

