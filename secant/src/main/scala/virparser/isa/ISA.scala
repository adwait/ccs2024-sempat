package virparser
package isa



abstract class ISA {
    val ABIMap : Map[String, Int]
    val instructions : Map[String, (List[String], Map[String, Int])]

    def parseInst (inst: VIRInstruction) : (VIRInstruction, Map[String, Int]) = {
        instructions.get(inst.opcode.opcode) match {
            case Some(params) => {
                val paramMap = params._1.zip(inst.operands).map(p => (p._1, p._2 match {
                    case InstIdOp(name) => ABIMap.get(name) match {
                        case Some(id) => id
                        case None => throw new Exception("Unknown ABI name: " + name)
                    }
                    case InstImmOp(imm) => imm
                })).toMap
                (inst, paramMap.++:(params._2))
            }
            case None => throw new Exception("Unknown instruction: " + inst.opcode.opcode)
        }
    }
}
