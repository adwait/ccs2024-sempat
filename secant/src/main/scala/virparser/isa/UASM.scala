package virparser
package isa


object UASM extends ISA {

    val ABINames = List("zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "s1", 
        "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7", 
        "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11", 
        "t3", "t4", "t5", "t6")
    val ABIMap = ABINames.zipWithIndex.toMap
    val ABIMapRev = ABIMap.map(_.swap)

    val instructions = Map(
        "call" -> (List("imm"), Map.empty),
        "skip" -> (List.empty, Map.empty),
        "ret" -> (List.empty, Map.empty),
        "add" -> (List("rd", "rs1", "imm"), Map.empty),
        "load" -> (List("rd", "rs1", "imm"), Map.empty),
        "store" -> (List("rs1", "rs2", "imm"), Map.empty),
        "beqz" -> (List("rs1", "imm"), Map.empty)
    )

    /**
      * For a given atomic block and an instruction in the block,
      * identify all instructions that are a dependency of this instruction.
      * 
      *
      * @param instid
      * @param virab
      * @return
      */
    def traceBack (instid: Int, virab: VIRAtomicBlock) : List[Int] = {
        val inst = virab.instructions(instid)
        val taintfields = collection.mutable.Set[InstOperand](inst.operands.drop(1).filter(_.isInstanceOf[InstIdOp]): _*)
        
        val precedinginsts = (virab.instructions.zipWithIndex).take(instid).reverse

        val deps = precedinginsts.foldLeft((List[Int](), taintfields))((acc, inst) => {
            if (inst._1.opcode.opcode == "add") {
                val op0 = inst._1.operands(0)
                val op1 = inst._1.operands(1)
                if (taintfields.contains(op0)) {
                    acc._2.remove(op0)
                    acc._2.add(op1)
                    (inst._2 :: acc._1, acc._2)
                } else acc
            } else if (inst._1.opcode.opcode == "load") {
                val op0 = inst._1.operands(0)
                val op1 = inst._1.operands(1)
                if (!taintfields.contains(op0)) acc
                else if (op1 == InstIdOp("s0")) {
                    acc._2.remove(op0)
                    (inst._2 :: acc._1, acc._2)
                } else {
                    acc._2.remove(op0)
                    acc._2.add(op1)
                    (inst._2 :: acc._1, acc._2)
                }
            } else acc
        })
        deps._1
    }
}