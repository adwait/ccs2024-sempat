package secant

package analyzers


import platforms.BVSSPlatform

import secant.flang.FLang._
import secant.flang._
import secant.tableau._
import virparser.{VIRInstruction, VIRAtomicBlock, PEvalInfo}
import virparser.isa.RV32UI


class BVSSPlatformAnalyzer(platform: BVSSPlatform) extends PlatformAnalysisConfig with IsProgramAnalyzer {

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
            // TODO: might lead to an issue if the immediate is negative (UCLID bitvecs are unsigned?)
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
                    // operandMapping.get(param) match {
                    //     case None => None
                    //     case Some(value) => Some()
                    // }
                })))
            }
        }
    }

    /**
      * Matcher that returns dependency filtered matches of Tableau 
      * template in the VIRAtomicBlock.
      *
      * @param virab
      * @param tabl
      * @return
      */
    override def getTableauMatches (virab: VIRAtomicBlock, peval: List[Option[PEvalInfo]], tabl: AbsTableau) : List[List[Int]] = {

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

override val tableaus = List(
        FlatTableau(List((2, StoreOp), (1, LoadOp), (0, StoreOp)),
            List(List.empty, List.empty, List.empty),
            List(FacetPredicateFlowDef(Utils.llp(StoreOp.addr, 2, StoreOp) === Utils.llp(LoadOp.addr, 1, LoadOp)),
                FacetPredicateFlowDef(Utils.llp(StoreOp.addr, 2, StoreOp) === Utils.llp(StoreOp.addr, 0, StoreOp))),
            List.empty
        )
    )

}

object BVSSPlatformAnalyzer {
    def apply(platform: MicroPlatform) : BVSSPlatformAnalyzer = {
        platform match {
            case p: BVSSPlatform => new BVSSPlatformAnalyzer(p)
            case _ => SemPatDriver.ERROR("BVSSPlatformAnalyzer can only be used with BVSSPlatform")
        }
    }
}

class BVSSPlatformTableauGenerator (platform: BVSSPlatform, genconf: Map[String, Int]) extends PlatformAnalysisConfig with IsTableauGenerator {

    import platform._

    val facets = Map(
        LoadOp -> List(LoadOp.rd),
        StoreOp -> List(StoreOp.rs1),
        ALUIOp -> List(ALUIOp.op1, ALUIOp.op2)
    )

    val flow : Map[TableauFlowEdge, (Int, Int) => FacetPredicate] = Map(
        // Address dependencies
        TableauFlowEdge("addr", LoadOp, StoreOp) -> ((i, j) => 
            FacetPredicateAddrDep(Utils.llp(LoadOp.rd, i, LoadOp) === Utils.llp(StoreOp.rs1, j, StoreOp))),
        TableauFlowEdge("addr", LoadOp, LoadOp) -> ((i, j) => 
            FacetPredicateAddrDep(Utils.llp(LoadOp.rd, i, LoadOp) === Utils.llp(LoadOp.rs1, j, LoadOp))),
        TableauFlowEdge("addr", ALUIOp, StoreOp) -> ((i, j) => 
            FacetPredicateAddrDep(Utils.llp(ALUIOp.rd, i, ALUIOp) === Utils.llp(StoreOp.rs1, j, StoreOp))),
        TableauFlowEdge("addr", ALUIOp, LoadOp) -> ((i, j) => 
            FacetPredicateAddrDep(Utils.llp(ALUIOp.rd, i, ALUIOp) === Utils.llp(LoadOp.rs1, j, LoadOp))),
        // Addr independency
        TableauFlowEdge("addr_indep", StoreOp, LoadOp) -> ((i, j) => 
            FacetPredicateAddrDep(Utils.llp(StoreOp.addr, i, StoreOp) !== Utils.llp(LoadOp.addr, j, LoadOp))),
        // TableauFlowEdge("no_cons", StoreOp, LoadOp) -> ((i, j) => trueLit),
        // Data dependencies
        TableauFlowEdge("data", LoadOp, ALUIOp) -> ((i, j) => 
            FacetPredicateDataDep(Utils.llp(LoadOp.rd, i, LoadOp) === Utils.llp(ALUIOp.rs1, j, ALUIOp))),
        TableauFlowEdge("data", LoadOp, StoreOp) -> ((i, j) => 
            FacetPredicateDataDep(Utils.llp(LoadOp.rd, i, LoadOp) === Utils.llp(StoreOp.rs2, j, StoreOp))),
        // Either data or address is dependent
        TableauFlowEdge("data_or_addr", LoadOp, StoreOp) -> ((i, j) => 
            FacetPredicateAddrDep((Utils.llp(LoadOp.rd, i, LoadOp) === Utils.llp(StoreOp.rs1, j, StoreOp)) 
            || (Utils.llp(LoadOp.rd, i, LoadOp) === Utils.llp(StoreOp.rs2, j, StoreOp)))),
        // TableauFlowEdge("data", StoreOp, LoadOp) -> ((i, j) => (Utils.llp(StoreOp.addr, i, StoreOp) === Utils.llp(LoadOp.addr, j, LoadOp))),
        // Address hashing dependencies
        TableauFlowEdge("addrhash_eq", StoreOp, StoreOp) -> ((i, j) => 
            FacetPredicateFlowDef(Utils.llp(StoreOp.addr_hash, i, StoreOp) === Utils.llp(StoreOp.addr_hash, j, StoreOp))
            // && (Utils.llp(StoreOp.addr, i, StoreOp) !== Utils.llp(StoreOp.addr, j, StoreOp))
        ),
        TableauFlowEdge("addrhash_ineq", StoreOp, StoreOp) -> ((i, j) => 
            FacetPredicateFlowDef(Utils.llp(StoreOp.addr_hash, i, StoreOp) !== Utils.llp(StoreOp.addr_hash, j, StoreOp))
        ),
        // 
        TableauFlowEdge("data", ALUIOp, StoreOp) -> ((i, j) => 
            FacetPredicateDataDep(Utils.llp(ALUIOp.rd, i, ALUIOp) === Utils.llp(StoreOp.rs2, j, StoreOp))),
        TableauFlowEdge("data", ALUIOp, ALUIOp) -> ((i, j) => 
            FacetPredicateDataDep(Utils.llp(ALUIOp.rd, i, ALUIOp) === Utils.llp(ALUIOp.rs1, j, ALUIOp))),
    )

    val flowt = Map[TableauFlowEdge, (Int, Int) => FacetPredicate](
        (TableauFlowEdge("same_addr", StoreOp, StoreOp) -> 
            ((i, j) => FacetPredicateAddrDep(Utils.llp(StoreOp.addr, i, StoreOp) === Utils.llp(StoreOp.addr, j, StoreOp)))),
        (TableauFlowEdge("diff_addr", StoreOp, StoreOp) -> (
            (i, j) => FacetPredicateAddrDep(Utils.llp(StoreOp.addr, i, StoreOp) !== Utils.llp(StoreOp.addr, j, StoreOp))))
    ).++(flow)

    val secannotation = PrePostAnnotation (
        pre = Map(regfile -> Public(), lscount -> Public(), lsqc_addr -> Public(), 
            lsqc_data -> Public(), lsqc_valid -> Public(), lsptr -> Public(), mem -> Secret()),
        post = Map(lscount -> Public()),
        init = (0 until lsqc_size).foldRight[FExpr](trueLit)((i, fe) => (fe && (lsqc_valid(bv(i, lsqc_setind_width+lsqc_wayind_width)) === falseLit)))
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

object BVSSPlatformTableauGenerator {
    def apply(platform: MicroPlatform, genconfig: Map[String, Int]) : BVSSPlatformTableauGenerator = {
        platform match {
            case p: BVSSPlatform => new BVSSPlatformTableauGenerator(p, genconfig)
            case _ => SemPatDriver.ERROR("BVSSPlatformTableauGenerator can only be used with BVSSPlatform")
        }
    }
}