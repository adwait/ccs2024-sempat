package virparser
package isa


object RV32UI extends ISA {

    val ABINames = List("zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "s1", 
        "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7", 
        "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11", 
        "t3", "t4", "t5", "t6")
    val ABIMap = ABINames.zipWithIndex.toMap
    val ABIMapRev = ABIMap.map(_.swap)

    val instructions = Map(
        "lui" -> (List("rd", "imm"), Map("funct3" -> 0)),
        "auipc" -> (List("rd", "imm"), Map("funct3" -> 0)),
        
        // Arithmetic immediate
        "addi" -> (List("rd", "rs1", "imm"), Map("funct3" -> 0)),
        "slti" -> (List("rd", "rs1", "imm"), Map("funct3" -> 2)),
        "sltiu" -> (List("rd", "rs1", "imm"), Map("funct3" -> 3)),
        "xori" -> (List("rd", "rs1", "imm"), Map("funct3" -> 4)),
        "ori" -> (List("rd", "rs1", "imm"), Map("funct3" -> 6)),
        "andi" -> (List("rd", "rs1", "imm"), Map("funct3" -> 7)),
        "slli" -> (List("rd", "rs1", "imm"), Map("funct3" -> 1)),
        "srli" -> (List("rd", "rs1", "imm"), Map("funct3" -> 5)),
        "srai" -> (List("rd", "rs1", "imm"), Map("funct3" -> 5)),
        // Treat addiw as addi
        "addiw" -> (List("rd", "rs1", "imm"), Map("funct3" -> 0)),
        "slliw" -> (List("rd", "rs1", "imm"), Map("funct3" -> 1)),
        "sraiw" -> (List("rd", "rs1", "imm"), Map("funct3" -> 5)),

        // Arithmetic register
        "add" -> (List("rd", "rs1", "rs2"), Map("funct3" -> 0, "funct7" -> 0)),
        "sub" -> (List("rd", "rs1", "rs2"), Map("funct3" -> 0, "funct7" -> 32)),
        "subw" -> (List("rd", "rs1", "rs2"), Map("funct3" -> 0, "funct7" -> 32)),
        "slt" -> (List("rd", "rs1", "rs2"), Map("funct3" -> 2, "funct7" -> 0)),
        "sltu" -> (List("rd", "rs1", "rs2"), Map("funct3" -> 3, "funct7" -> 0)),
        "xor" -> (List("rd", "rs1", "rs2"), Map("funct3" -> 4, "funct7" -> 0)),
        "or" -> (List("rd", "rs1", "rs2"), Map("funct3" -> 6, "funct7" -> 0)),
        "and" -> (List("rd", "rs1", "rs2"), Map("funct3" -> 7, "funct7" -> 0)),
        "sll" -> (List("rd", "rs1", "rs2"), Map("funct3" -> 1, "funct7" -> 0)),
        "srl" -> (List("rd", "rs1", "rs2"), Map("funct3" -> 5, "funct7" -> 0)),
        "sra" -> (List("rd", "rs1", "rs2"), Map("funct3" -> 5, "funct7" -> 32)),
        "sraw" -> (List("rd", "rs1", "rs2"), Map("funct3" -> 5, "funct7" -> 32)),

        // Multiplication
        "mulw" -> (List("rd", "rs1", "rs2"), Map.empty),
        "mul" -> (List("rd", "rs1", "rs2"), Map.empty),
        
        // Loads
        "lw" -> (List("rd", "rs1", "imm"), Map.empty),
        "lb" -> (List("rd", "rs1", "imm"), Map.empty),
        "lh" -> (List("rd", "rs1", "imm"), Map.empty),
        "lbu" -> (List("rd", "rs1", "imm"), Map.empty),
        "lhu" -> (List("rd", "rs1", "imm"), Map.empty),
        "ld" -> (List("rd", "rs1", "imm"), Map.empty),
        "lwu" -> (List("rd", "rs1", "imm"), Map.empty),
        // Stores
        "sw" -> (List("rs2", "rs1", "imm"), Map.empty),
        "sb" -> (List("rs2", "rs1", "imm"), Map.empty),
        "sh" -> (List("rs2", "rs1", "imm"), Map.empty),
        "sd" -> (List("rs2", "rs1", "imm"), Map.empty),
        
        // Branches
        "beq" -> (List("rs1", "rs2", "imm"), Map("funct3" -> 0)),
        "bne" -> (List("rs1", "rs2", "imm"), Map("funct3" -> 1)),
        "blt" -> (List("rs1", "rs2", "imm"), Map("funct3" -> 4)),
        "bge" -> (List("rs1", "rs2", "imm"), Map("funct3" -> 5)),
        "bltu" -> (List("rs1", "rs2", "imm"), Map("funct3" -> 6)),
        "bgeu" -> (List("rs1", "rs2", "imm"), Map("funct3" -> 7)),

        // Jumps
        "jal" -> (List("rd", "imm"), Map.empty),
        "jalr" -> (List("rd", "rs1", "imm"), Map.empty)
    )


    val alui = List("addi", "slti", "sltiu", "xori", "ori", "andi", "slli", "srli", "srai", "addiw")
    val alur = List("add", "sub", "subw", "slt", "sltu", "xor", "or", "and", "sll", "srl", "sra", "mulw", "mul")
    val load = List("lw", "lb", "lh", "lbu", "lhu", "ld", "lwu")
    val store = List("sw", "sb", "sh", "sd")
    val branch = List("beq", "bne", "blt", "bge", "bltu")
    val jump = List("jal", "jalr")

    sealed abstract class DepAnalysisStrategy
    case object DepAnalysisDefault extends DepAnalysisStrategy
    case object DepAnalysisFirstHit extends DepAnalysisStrategy
    case object DepAnalysisWithPEval extends DepAnalysisStrategy

    // Taint analysis can only be intraprocedural (fixed stack pointer)
    case class TraceContext (regs: Set[InstOperand], memlocs: Set[Address]) {
        def addReg (reg: InstOperand) : TraceContext = TraceContext(regs + reg, memlocs)
        def remReg (reg: InstOperand) : TraceContext = TraceContext(regs - reg, memlocs)

        def addMem (loc: Address) : TraceContext = TraceContext(regs, memlocs + loc)
        def remMem (loc: Address) : TraceContext = TraceContext(regs, memlocs - loc)

        def repReg (regnew : InstOperand, regold : InstOperand) = TraceContext(regs - regold + regnew, memlocs)
    }
    /**
      * For a given atomic block and an instruction in the block,
      * identify all instructions that are a dependency of this instruction.
      * 
      *
      * @param instid
      * @param virab
      * @return
      */
    //   This is the main dep analysis function, which further calls other based on the strategy
    def traceBack (instid: Int, virab: VIRAtomicBlock, strategy: DepAnalysisStrategy = DepAnalysisDefault, 
        pevals: List[Option[PEvalInfo]] = List.empty) : List[Int] = {
        strategy match {
            case DepAnalysisDefault => traceBackDefault(instid, virab)
            case DepAnalysisFirstHit => traceBackFirstHit(instid, virab)
            case DepAnalysisWithPEval => {
                assert(false, "Taint analysis: PEval info not available for all instructions")
                assert(pevals.length == virab.instructions.length, "Taint analysis: PEval info not available for all instructions")
                throw new Error("Taint analysis: PEval info not available for all instructions")
            }
        }
    }

    def traceBackDefault (instid: Int, virab: VIRAtomicBlock) : List[Int] = {
        val inst = virab.instructions(instid)
        val taintfields = TraceContext (
            Set[InstOperand](inst.operands.drop(1).filter(_.isInstanceOf[InstIdOp]): _*),
            Set.empty
        )
        
        val precedinginsts = (virab.instructions.zipWithIndex).take(instid).reverse

        val deps = precedinginsts.foldLeft((List[Int](), taintfields))((acc, inst) => {
            if (alui.contains(inst._1.opcode.opcode)) {
                // op0: rd, op1: rs1
                val op0 = inst._1.operands(0)
                val op1 = inst._1.operands(1)
                if (acc._2.regs.contains(op0)) {
                    (inst._2::acc._1, acc._2.repReg(op1, op0))
                } else acc
            } else if (alur.contains(inst._1.opcode.opcode)) {
                // op0: rd, op1: rs1, op2: rs2
                val op0 = inst._1.operands(0)
                val op1 = inst._1.operands(1)
                val op2 = inst._1.operands(2)
                if (acc._2.regs.contains(op0)) {
                    (inst._2::acc._1, acc._2.remReg(op0).addReg(op1).addReg(op2))
                } else acc
            } else if (load.contains(inst._1.opcode.opcode)) {
                // op0: rd, op1: rs1, op2: imm
                val op0 = inst._1.operands(0)
                val op1 = inst._1.operands(1)
                val op2 = inst._1.operands(2)
                // If destination is untainted
                if (!acc._2.regs.contains(op0)) acc
                // Stack offset
                else if (op1 == InstIdOp("s0")) {
                    op2 match {
                        case _: InstIdOp => throw new Error("Taint analysis: stack offset is not a constant")
                        case imm: InstImmOp => (inst._2::acc._1, acc._2.remReg(op0))
                    }
                } else {               
                    (inst._2::acc._1, acc._2.remReg(op0).addReg(op1))
                }
            } else acc
        })
        deps._1
    }

    def traceBackFirstHit (instid: Int, virab: VIRAtomicBlock) : List[Int] = {
        val inst = virab.instructions(instid)
        val taintfields = TraceContext (
            Set[InstOperand](inst.operands.drop(1).filter(_.isInstanceOf[InstIdOp]): _*),
            Set.empty
        )
        
        val precedinginsts = (virab.instructions.zipWithIndex).take(instid).reverse

        val deps = precedinginsts.foldLeft((List[Int](), taintfields))((acc, inst) => {
            if (alui.contains(inst._1.opcode.opcode)) {
                // op0: rd, op1: rs1
                val op0 = inst._1.operands(0)
                val op1 = inst._1.operands(1)
                if (acc._2.regs.contains(op0)) {
                    (inst._2::acc._1, acc._2.remReg(op0))
                } else acc
            } else if (alur.contains(inst._1.opcode.opcode)) {
                // op0: rd, op1: rs1, op2: rs2
                val op0 = inst._1.operands(0)
                val op1 = inst._1.operands(1)
                val op2 = inst._1.operands(2)
                if (acc._2.regs.contains(op0)) {
                    (inst._2::acc._1, acc._2.remReg(op0))
                } else acc
            } else if (load.contains(inst._1.opcode.opcode)) {
                // op0: rd, op1: rs1, op2: imm
                val op0 = inst._1.operands(0)
                val op1 = inst._1.operands(1)
                val op2 = inst._1.operands(2)
                // If destination is untainted
                if (!acc._2.regs.contains(op0)) acc
                // Stack offset
                else if (op1 == InstIdOp("s0")) {
                    op2 match {
                        case _: InstIdOp => throw new Error("Taint analysis: stack offset is not a constant")
                        case imm: InstImmOp => (inst._2::acc._1, acc._2.remReg(op0))
                    }
                } else {               
                    (inst._2::acc._1, acc._2.remReg(op0))
                }
            } else acc
        })
        deps._1
    }

}