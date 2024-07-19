package secant

package analyzers

import platforms.BVLSQCachePlatform

import flang.FLang._
import flang._
import tableau._
import virparser.{VIRInstruction, VIRAtomicBlock, PEvalInfo, Address, ConcVal, Top}
import virparser.isa.RV32UI

class BVLSQCachePlatformAnalyzer(platform: BVLSQCachePlatform, anconfig: Map[String, Int]) extends PlatformAnalysisConfig with IsProgramAnalyzer {

    import platform._

    val facets = Map(
        LoadOp -> List(LoadOp.rd, LoadOp.rs1),
        StoreOp -> List(StoreOp.addr, StoreOp.data, StoreOp.rs1, StoreOp.rs2),
        ALUIOp -> List(ALUIOp.op1, ALUIOp.op2),
        ALUROp -> List(ALUROp.op1, ALUROp.op2)
    )

    val secannotation = PrePostAnnotation (
        pre = Map(regfile -> Public(), lscount -> Public(), lsqc_addr -> Public(), 
            lsqc_data -> Public(), lsqc_valid -> Public(), lsptr -> Public(), mem -> Secret()),
        post = Map(lscount -> Public())
    )

    val opcodeMapping : Map[String, MicroOp] = Map(
        ALUIOp -> List("addi", "slli", "slti", "sltiu", "xori", "srli", "srai", "ori", "andi", "addiw", "slliw", "srliw", "sraiw", "lui"),
        ALUROp -> List("add", "sub", "subw", "sll", "slt", "sltu", "xor", "srl", "sra", "or", "and", "mulw", "mul"),
        LoadOp -> List("lw", "lb", "lh", "lbu", "lhu", "ld", "lwu"),
        StoreOp -> List("sw", "sb", "sh", "sd")
    ).flatMap(pair => pair._2.map(mop => (mop, pair._1)))

    def setOperandValue (flp: FLocalParam, v: Int) : FNLit = {
        flp match {
            case ALUIOp.rs1 | LoadOp.rs1 | StoreOp.rs1 => bv(v, 5)
            case ALUIOp.rs1 | ALUROp.rs2 | StoreOp.rs2 => bv(v, 5)
            case ALUIOp.rd |  ALUROp.rd | LoadOp.rd => bv(v, 5)
            // INFO: might lead to an issue if the immediate is negative (UCLID bitvecs are unsigned?)
            case LoadOp.imm | StoreOp.imm | ALUIOp.imm => bv(if (v >= 0) v else ((1 << 12)+v), 32)
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
                })))
            }
        }
    }

    def matcher1 (virab: VIRAtomicBlock, tabl: AbsTableau) : List[List[Int]] = {
        // Reverse sequence of the tableau sequence in the pattern
        val rtmopseq = tabl.tableauSeq.map(_._2).reverse
        // Extract the sequence of micro-operations from the atomic block
        val pmopseq = virab.instructions.map(vircomp(_, None).mop)
        
        // Find match indices for first micro-op in tableau
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
                    case _ => true
                }
            }
        }

        assert (virab.instructions.length == pevals.length, "Matcher2: VIRAtomicBlock and PEvalInfo list length mismatch.")

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

        // val iseqs = pmopseq.zipWithIndex.filter(p => rtmopseq(0) == p._1).map(p => List(p._2))
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
                // }).filter(i => {
                //     isIFPredicateSatisfied(pevals(i), mop_infmops_pred)
                }).map(i => {
                    i :: iseq
                })
            })
        })
        SemPatDriver.DEBUG(s"Matches: ${matches}")
        matches
    }



    /**
      * Matcher that returns dependency filtered matches of Tableau 
      * template in the VIRAtomicBlock.
      *
      * @param virab
      * @param tabl
      * @return
      */
    override def getTableauMatches (virab: VIRAtomicBlock, pevals: List[Option[PEvalInfo]], tabl: AbsTableau) : List[List[Int]] = {
        if (anconfig.getOrElse("matcher", 1) == 1) matcher1 (virab, tabl) 
        else { tabl match {
            case t: FlowTableau => matcher2 (virab, t, pevals)
            case _ => SemPatDriver.ERROR("Matcher 2 only accepts flow tableau.")
        }}
        
    }

    override val tableaus = List(

        if (anconfig.getOrElse("tabchoice", 0) == 0)
            FlowTableau(List((2, LoadOp), (1, StoreOp), (0, LoadOp)),
                List(
                    List(LoadOp, StoreOp, ALUIOp, ALUROp, NOP),
                    List(ALUIOp, ALUROp, NOP),
                    List(ALUIOp, ALUROp, NOP)
                ),
                List(
                    FacetPredicateFlowDef(Utils.llp(LoadOp.addr, 2, LoadOp) !== Utils.llp(StoreOp.addr, 1, StoreOp)),
                    FacetPredicateFlowDef(trueLit)
                ),
                List(FacetPredicateIFDef(trueLit), FacetPredicateIFDef(trueLit), FacetPredicateIFHighResult(trueLit)),
                List.empty, List.empty
            )
        else FlowTableau(List((2, LoadOp), (1, StoreOp), (0, LoadOp)),
                List(
                    List(LoadOp, StoreOp, ALUIOp, ALUROp, NOP),
                    List(ALUIOp, ALUROp, NOP),
                    List(ALUIOp, ALUROp, NOP)
                ),
                List(
                    FacetPredicateFlowDef(Utils.llp(LoadOp.addr_hash, 2, LoadOp) !== Utils.llp(StoreOp.addr_hash, 1, StoreOp)),
                    FacetPredicateFlowDef(trueLit)
                ),
                List(FacetPredicateIFDef(trueLit), FacetPredicateIFDef(trueLit), FacetPredicateIFHighResult(trueLit)),
                List.empty, List.empty
            ),
        FlowTableau(List((1, LoadOp), (0, LoadOp)),
            List(
                List(LoadOp, StoreOp, ALUIOp, ALUROp, NOP),
                List(ALUIOp, ALUROp, NOP)
            ),
            List(
                FacetPredicateFlowDef(trueLit)
            ),
            List(FacetPredicateIFDef(trueLit), FacetPredicateIFHighResult(trueLit)),
            List.empty, List.empty
        )
    )

}

object BVLSQCachePlatformAnalyzer {
    def apply(platform: MicroPlatform, anconfig: Map[String, Int]) : BVLSQCachePlatformAnalyzer = {
        platform match {
            case p: BVLSQCachePlatform => new BVLSQCachePlatformAnalyzer(p, anconfig)
            case _ => SemPatDriver.ERROR("BVLSQCachePlatformAnalyzer can only be used with BVLSQCachePlatform")
        }
    }
}

class BVLSQCachePlatformTableauGenerator (platform: BVLSQCachePlatform, genconf: Map[String, Int]) extends PlatformAnalysisConfig with IsTableauGenerator {

    import platform._

    val facets = Map(
        LoadOp -> List(LoadOp.rd),
        StoreOp -> List(StoreOp.rs1),
        ALUIOp -> List(ALUIOp.op1, ALUIOp.op2)
    )

    val flow : Map[TableauFlowEdge, (Int, Int) => FacetPredicate] = Map(
        // Address dependencies
        TableauFlowEdge("addr", LoadOp, LoadOp) -> ((i, j) => 
            FacetPredicateAddrDep(Utils.llp(LoadOp.rd, i, LoadOp) === Utils.llp(LoadOp.rs1, j, LoadOp))),
        TableauFlowEdge("addrhash_ineq", StoreOp, StoreOp) -> ((i, j) => 
            FacetPredicateFlowDef(Utils.llp(StoreOp.addr_hash, i, StoreOp) !== Utils.llp(StoreOp.addr_hash, j, StoreOp))),
        (TableauFlowEdge("addrhash_ineq", LoadOp, StoreOp) -> 
            ((i, j) => FacetPredicateFlowDef(Utils.llp(LoadOp.addr_hash, i, LoadOp) !== Utils.llp(StoreOp.addr_hash, j, StoreOp)))),
        TableauFlowEdge("data", ALUIOp, StoreOp) -> ((i, j) => 
            FacetPredicateDataDep(Utils.llp(ALUIOp.rd, i, ALUIOp) === Utils.llp(StoreOp.rs2, j, StoreOp))),
        TableauFlowEdge("data", ALUIOp, ALUIOp) -> ((i, j) => 
            FacetPredicateDataDep(Utils.llp(ALUIOp.rd, i, ALUIOp) === Utils.llp(ALUIOp.rs1, j, ALUIOp))),
    )

    val flowt = Map[TableauFlowEdge, (Int, Int) => FacetPredicate](
        (TableauFlowEdge("same_addr", StoreOp, StoreOp) -> 
            ((i, j) => FacetPredicateAddrDep(Utils.llp(StoreOp.addr, i, StoreOp) === Utils.llp(StoreOp.addr, j, StoreOp)))),
        (TableauFlowEdge("diff_addr", StoreOp, StoreOp) -> (
            (i, j) => FacetPredicateAddrDep(Utils.llp(StoreOp.addr, i, StoreOp) !== Utils.llp(StoreOp.addr, j, StoreOp)))),
        (TableauFlowEdge("diff_addr", LoadOp, StoreOp) -> 
            ((i, j) => FacetPredicateAddrDep(Utils.llp(LoadOp.addr, i, LoadOp) !== Utils.llp(StoreOp.addr, j, StoreOp)))),
    ).++(flow)

    val secannotation = PrePostAnnotation (
        pre = Map(regfile -> Public(), lscount -> Public(), lsqc_addr -> Public(), 
            lsqc_data -> Public(), lsqc_valid -> Public(), lsptr -> Public(), mem -> Secret()),
        post = Map(lscount -> Public()),
        init = (0 until lsqc_size).foldRight[FExpr](trueLit)((i, fe) => (fe && (lsqc_valid(bv(i, lsqc_setind_width+lsqc_wayind_width)) === falseLit))),
        prune = false
    )

    val grammardepth = genconf.getOrElse("grammardepth", 3)

    val spectype = if (genconf.getOrElse("spectype", 0) == 0) "tree" else "treemulti"

    val tgconfig = List(
        // FlowTableauSpecification(
        //     "flow", spec = secannotation, flows = flow, depth = 3
        // ),
        if (spectype == "tree")
            TreeTableauSpecification(
                "tree", spec = secannotation, edges = flowt, iflabels = Map.empty, 
                depth = grammardepth, wneg = true
            )
        else 
            TreeTableauSpecificationMultiCon(
                "tree", spec = secannotation, edges = flowt, iflabels = Map.empty, 
                depth = grammardepth, wneg = true
            )
    )
}

object BVLSQCachePlatformTableauGenerator {
    def apply(platform: MicroPlatform, genconfig: Map[String, Int]) : BVLSQCachePlatformTableauGenerator = {
        platform match {
            case p: BVLSQCachePlatform => new BVLSQCachePlatformTableauGenerator(p, genconfig)
            case _ => SemPatDriver.ERROR("BVLSQCachePlatformTableauGenerator can only be used with BVLSQCachePlatform")
        }
    }
}