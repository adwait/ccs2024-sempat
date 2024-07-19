/*
 * SemPat Project.
 * 
 * @file ProgramTaintAnalysis.scala
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
 * Performs syntactic taint analysis of a VIRProgram.
 *
 */

package virparser

import scala.collection.mutable.Map
import scala.collection.immutable.ListMap


sealed abstract class AbsValue {
    def +(that: AbsValue): AbsValue
    def -(that: AbsValue): AbsValue
    def <(that: AbsValue): AbsValue
    def >=(that: AbsValue): AbsValue
    def ==(that: AbsValue): AbsValue
    def !=(that: AbsValue): AbsValue
    def &(that: AbsValue): AbsValue
    def |(that: AbsValue): AbsValue
    def ^(that: AbsValue): AbsValue
    def <<(that: AbsValue): AbsValue
    def >>(that: AbsValue): AbsValue
    def >>>(that: AbsValue): AbsValue
    def :< (that: AbsValue): AbsValue
    def :>= (that: AbsValue): AbsValue

    def * (that: AbsValue): AbsValue

    def &(that: Long): AbsValue
    def |(that: Long): AbsValue
    def <<(that: Long): AbsValue
    def >>>(that: Long): AbsValue
}

case class Address(a: Long, b: Boolean = false) extends AbsValue {
    def +(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(true)
        case ConcVal(v_, b_) => Address(a + v_, b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def +(that: Int): Address = Address(a + that, b)
    def -(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => ConcVal(a - a_, b || b_)
        case ConcVal(v_, b_) => Address(a - v_, b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def <(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => if (a < a_) ConcVal(1, b || b_) else ConcVal(0, b || b_)
        case ConcVal(v_, b_) => Top(b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def >=(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => if (a >= a_) ConcVal(1, b || b_) else ConcVal(0, b || b_)
        case ConcVal(v_, b_) => Top(b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def ==(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => if (a == a_) ConcVal(1, b || b_) else ConcVal(0, b || b_)
        case ConcVal(v_, b_) => Top(b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def !=(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => if (a != a_) ConcVal(1, b || b_) else ConcVal(0, b || b_)
        case ConcVal(v_, b_) => Top(b || b_)
        case Top(b_)         => Top(b || b_)
    }

    def *(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(b || b_)
        case ConcVal(v_, b_) => Top(b || b_)
        case Top(b_)         => Top(b || b_)
    }

    def &(that: AbsValue): AbsValue = Top(true)
    def |(that: AbsValue): AbsValue = Top(true)
    def ^(that: AbsValue): AbsValue = Top(true)
    def <<(that: AbsValue): AbsValue = Top(true)
    def >>(that: AbsValue): AbsValue = Top(true)
    def >>>(that: AbsValue): AbsValue = Top(true)
    def :< (that: AbsValue): AbsValue = this < that
    def :>= (that: AbsValue): AbsValue = this >= that
    def &(that: Long): AbsValue = Address(a & that, b)
    def |(that: Long): AbsValue = Address(a | that, b)
    def <<(that: Long): AbsValue = Address(a << that, b)
    def >>>(that: Long): AbsValue = Address(a >>> that, b)
    override def toString(): String = s"Address(${a}, ${b})"
}

case class ConcVal(v: Long, b: Boolean = false) extends AbsValue {
    def +(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Address(v + a_, b || b_)
        case ConcVal(v_, b_) => ConcVal(v + v_, b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def -(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(true)
        case ConcVal(v_, b_) => ConcVal(v - v_, b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def <(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(b || b_)
        case ConcVal(v_, b_) => if (v < v_) ConcVal(1, b || b_) else ConcVal(0, b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def >=(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(b || b_)
        case ConcVal(v_, b_) => if (v >= v_) ConcVal(1, b || b_) else ConcVal(0, b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def ==(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(b || b_)
        case ConcVal(v_, b_) => if (v == v_) ConcVal(1, b || b_) else ConcVal(0, b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def !=(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(b || b_)
        case ConcVal(v_, b_) => if (v != v_) ConcVal(1, b || b_) else ConcVal(0, b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def &(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(true)
        case ConcVal(v_, b_) => ConcVal(v & v_, b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def |(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(true)
        case ConcVal(v_, b_) => ConcVal(v | v_, b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def ^(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(true)
        case ConcVal(v_, b_) => ConcVal(v ^ v_, b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def <<(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(true)
        case ConcVal(v_, b_) => ConcVal(v << v_, b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def >>(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(true)
        case ConcVal(v_, b_) => ConcVal(v >> v_, b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def >>>(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(true)
        case ConcVal(v_, b_) => ConcVal(v >>> v_, b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def :< (that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(b || b_)
        case ConcVal(v_, b_) => {
            if ((v_ >= 0 && v >= 0) || (v_ < 0 && v < 0)){
                if (v < v_) ConcVal(1, b || b_) else ConcVal(0, b || b_)
            } else if (v_ < 0 && v >= 0) {
                ConcVal(1)
            } else if (v_ >= 0 && v < 0) {
                ConcVal(0)
            } else {
                throw new RuntimeException("Should not reach here");
            }
        }
        case Top(b_)         => Top(b || b_)
    }
    def :>= (that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(b || b_)
        case ConcVal(v_, b_) => {
            if ((v_ >= 0 && v >= 0) || (v_ < 0 && v < 0)){
                if (v >= v_) ConcVal(1, b || b_) else ConcVal(0, b || b_)
            } else if (v_ < 0 && v >= 0) {
                ConcVal(0)
            } else if (v_ >= 0 && v < 0) {
                ConcVal(1)
            } else {
                throw new RuntimeException("Should not reach here");
            }
        }
        case Top(b_)         => Top(b || b_)
    }
    def * (that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(true)
        case ConcVal(v_, b_) => ConcVal(v * v_, b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def &(that: Long): AbsValue = ConcVal(v & that, b)
    def |(that: Long): AbsValue = ConcVal(v | that, b)
    def <<(that: Long): AbsValue = ConcVal(v << that, b)
    def >>>(that: Long): AbsValue = ConcVal(v >>> that, b)
    def unary_~(): ConcVal = ConcVal(~v, b)
    override def toString(): String = s"ConcVal(${v}, ${b})"
}

case class Top(b: Boolean) extends AbsValue {
    def +(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(b || b_)
        case ConcVal(v_, b_) => Top(b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def -(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(true)
        case ConcVal(v_, b_) => Top(b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def <(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(b || b_)
        case ConcVal(v_, b_) => Top(b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def >=(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(b || b_)
        case ConcVal(v_, b_) => Top(b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def ==(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(b || b_)
        case ConcVal(v_, b_) => Top(b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def !=(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(b || b_)
        case ConcVal(v_, b_) => Top(b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def &(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(true)
        case ConcVal(v_, b_) => Top(b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def |(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(true)
        case ConcVal(v_, b_) => Top(b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def ^(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(true)
        case ConcVal(v_, b_) => Top(b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def <<(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(true)
        case ConcVal(v_, b_) => Top(b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def >>(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(true)
        case ConcVal(v_, b_) => Top(b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def >>>(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(true)
        case ConcVal(v_, b_) => Top(b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def :< (that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(b || b_)
        case ConcVal(v_, b_) => Top(b || b_)
        case Top(b_)         => Top(b || b_)
    }
    def :>= (that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(b || b_)
        case ConcVal(v_, b_) => Top(b || b_)
        case Top(b_)         => Top(b || b_)
    }

    def *(that: AbsValue): AbsValue = that match {
        case Address(a_, b_) => Top(true)
        case ConcVal(v_, b_) => Top(b || b_)
        case Top(b_)         => Top(b || b_)
    }

    def &(that: Long): AbsValue = this
    def |(that: Long): AbsValue = this
    def <<(that: Long): AbsValue = this
    def >>>(that: Long): AbsValue = this
    override def toString(): String = s"Top(${b})"
}

// reg: reg name -> (val, high/low), stack: offset -> (val, high/low)
// Initialize all registers with (0, false)
case class TaintContext(var pc: AbsValue, 
                        reg: Map[String, AbsValue] = Map[String, AbsValue]("sp" -> Address(0), "ra" -> ConcVal(0)).withDefaultValue(Top(true)), 
                        stack: Map[Address, AbsValue] = Map[Address, AbsValue]().withDefaultValue(Top(true))) {
    override def toString() = {
        ("REG:\n" + reg.foldLeft("")((s, entry) => s + s"\t${entry._1} -> ${entry._2}\n") +
         "STACK:\n" + stack.foldLeft("")((s, entry) => s + s"\t${entry._1.a} -> ${entry._2}\n"))
        // reg.foldLeft("")((s, entry) => s + s"${entry._1} -> ${entry._2}\n") 
        //  "STACK:\n" + stack.foldLeft("")((s, entry) => s + s"\t${entry._1.a} -> ${entry._2}\n")
    }

    def printReg() : Unit = {
        println(s"pc: ${pc}")
        println("REG:")
        ListMap(reg.toSeq.sortBy(_._1):_*).foreach{case (k, v) => println(s"\t${k} -> ${v}")}
    }
    def printStack(): Unit = {
        println("STACK:")
        ListMap(stack.toSeq.sortBy(-_._1.a):_*).foreach{case (k, v) => println(s"\t${k.a} -> ${v}")}
    }
}

case class PEvalInfo(src1: InstIdOp, src2: InstIdOp, dest: InstIdOp, addr: AbsValue, arg1: AbsValue, arg2: AbsValue, res: AbsValue)

object ProgramTaintAnalysis {
    // val debug = true
    val debug = false
    val rtype = List("add", "sub", "xor", "or", "and", "sll", "srl", "sra", "slt", "sltu", "addw", "sllw", "srlw", "sraw")
    val load = List("lb", "lh", "lw", "ld", "lbu", "lhu", "lwu")
    val stype = List("sb", "sh", "sw", "sd")
    val itype = List("addi", "subi", "xori", "ori", "andi", "slli", "srli", "srai", "slti", "sltiu", "jalr", "ecall", "ebreak", "addiw", "slliw", "sraiw")
    val jtype = List("jal")
    val btype = List("beq", "bne", "blt", "bge", "bltu", "bgeu")
    val utype = List("lui", "aupic")
    val mul = List("mul", "mulw")
    val mask_8  = 0x00000000000000FFL
    val mask_16 = 0x000000000000FFFFL
    val mask_32 = 0x00000000FFFFFFFFL
    val mask_64 = 0xFFFFFFFFFFFFFFFFL

    def updateContext(inst: VIRInstruction, context: TaintContext): (TaintContext, Option[PEvalInfo]) = {
        // Helper function for sign extension
        def signExtend(x: AbsValue, n: Int) : AbsValue = {
            if (x.isInstanceOf[Top]) return x
            assert(x.isInstanceOf[ConcVal], s"${x.getClass}")
            val v = x.asInstanceOf[ConcVal].v
            val extend1 = ((v >> (n-1)) & 1L) == 1L
            if (extend1) x | (mask_64 << n) else x & (mask_64 >>> (64-n))
        }

        if (debug) {
            println(inst)
        }
        var updop : Option[PEvalInfo] = None
        val newContext = context.copy(pc=context.pc, reg=context.reg.clone(), stack=context.stack.clone())
        val opcode = inst.opcode.opcode
        if (rtype.contains(opcode)) {
            val op0 = inst.operands(0).asInstanceOf[InstIdOp].reg
            val op1 = inst.operands(1).asInstanceOf[InstIdOp].reg
            val op2 = inst.operands(2).asInstanceOf[InstIdOp].reg
            val a1 = newContext.reg(op1)
            val a2 = newContext.reg(op2)
            val nval = opcode match {
                case "add"  => newContext.reg(op1) + newContext.reg(op2)
                case "sub"  => newContext.reg(op1) - newContext.reg(op2)
                case "xor"  => newContext.reg(op1) ^ newContext.reg(op2)
                case "or"   => newContext.reg(op1) | newContext.reg(op2)
                case "and"  => newContext.reg(op1) & newContext.reg(op2)
                case "sll"  => newContext.reg(op1) << newContext.reg(op2)
                case "srl"  => newContext.reg(op1) >>> newContext.reg(op2)
                case "sra"  => newContext.reg(op1) >> newContext.reg(op2)
                case "slt"  => newContext.reg(op1) < newContext.reg(op2)
                case "sltu" => newContext.reg(op1) :< newContext.reg(op1)
                case "addw" => signExtend((newContext.reg(op1) + newContext.reg(op2)) & mask_32, 32)
                case "sllw" => signExtend((newContext.reg(op1) << newContext.reg(op2)) & mask_32, 32)
                case "srlw" => signExtend((newContext.reg(op1) & mask_32) >>> newContext.reg(op2), 32)
                case "sraw" => signExtend((newContext.reg(op1) & mask_32) >> newContext.reg(op2), 32)
                case _ => throw new NotImplementedError 
            }
            updop = Some(PEvalInfo(InstIdOp(op1), InstIdOp(op2), InstIdOp(op0), Top(true), a1, a2, nval))
            newContext.reg(op0) = nval
            newContext.pc = newContext.pc + ConcVal(4)
        }
        else if (load.contains(opcode)) {
            val op0 = inst.operands(0).asInstanceOf[InstIdOp].reg
            val op1 = inst.operands(1).asInstanceOf[InstIdOp].reg
            val op2 = ConcVal(inst.operands(2).asInstanceOf[InstImmOp].imm)
            assert((newContext.reg(op1) + op2).isInstanceOf[Address], 
                    s"${newContext.reg(op1).getClass} + ${op2.getClass} = ${(newContext.reg(op1) + op2).getClass}")
            val stackAddr = (newContext.reg(op1) + op2).asInstanceOf[Address]
            val mem = newContext.stack(stackAddr)
            
            val a1 = newContext.reg(op1)
            val nval = opcode match {
                case "lb" => signExtend(mem, 8)
                case "lh" => signExtend(mem, 16)
                case "lw" => signExtend(mem, 32)
                case "ld" => (newContext.stack(stackAddr + 4), mem) match {
                    case (Address(a, b), Address(a_, b_)) => Address(a << 32 | a_, b || b_)
                    case (ConcVal(v, b), ConcVal(v_, b_)) => ConcVal(v << 32 | v_, b || b_)
                    case (Top(b), Top(b_)) => Top(b || b_)
                    case _ => throw new RuntimeException("Should not reach here")
                }
                case "lbu" => mem & mask_8
                case "lhu" => mem & mask_16
                case "lwu" => mem & mask_32
                case _ => throw new NotImplementedError 
            }
            updop = Some(PEvalInfo(InstIdOp(op1), InstIdOp("zero"), InstIdOp(op0), stackAddr, a1, Top(true), nval))
            newContext.reg(op0) = nval
            newContext.pc = newContext.pc + ConcVal(4)
        }
        else if (stype.contains(opcode)) {
            val op0 = inst.operands(0).asInstanceOf[InstIdOp].reg
            val op1 = inst.operands(1).asInstanceOf[InstIdOp].reg
            val op2 = ConcVal(inst.operands(2).asInstanceOf[InstImmOp].imm)
            assert((newContext.reg(op1) + op2).isInstanceOf[Address])
            val stackAddr = (newContext.reg(op1) + op2).asInstanceOf[Address]

            val a1 = newContext.reg(op0)
            val nval = opcode match {
                case "sb" => newContext.reg(op0) & mask_8
                case "sh" => newContext.reg(op0) & mask_16
                case "sw" => newContext.reg(op0) & mask_32
                case "sd" => newContext.reg(op0) & mask_32
                case _ => throw new NotImplementedError 
            }
            newContext.stack(stackAddr) = nval
            if (opcode == "sd") {
                newContext.stack(stackAddr + 4) = newContext.reg(op0) >>> 32L
            }
            updop = Some(PEvalInfo(InstIdOp(op1), InstIdOp(op0), InstIdOp("zero"), stackAddr, a1, Top(true), nval))
            newContext.pc = newContext.pc + ConcVal(4)
        }
        else if (itype.contains(opcode)) {
            val op0 = inst.operands(0).asInstanceOf[InstIdOp].reg
            val op1 = inst.operands(1).asInstanceOf[InstIdOp].reg
            val op2 = ConcVal(inst.operands(2).asInstanceOf[InstImmOp].imm)

            val a1 = newContext.reg(op1)
            val nval = opcode match {
                case "addi"  => newContext.reg(op1) + op2
                case "subi"  => newContext.reg(op1) - op2
                case "xori"  => newContext.reg(op1) ^ op2
                case "ori"   => newContext.reg(op1) | op2
                case "andi"  => newContext.reg(op1) & op2
                case "slli"  => newContext.reg(op1) << op2
                case "srli"  => newContext.reg(op1) >>> op2
                case "srai"  => newContext.reg(op1) >> op2
                case "slti"  => newContext.reg(op1) < op2
                case "sltiu" => newContext.reg(op1) :< op2
                case "addiw" => signExtend(newContext.reg(op1) + op2, 32)
                case "slliw" => signExtend(newContext.reg(op1) << op2, 32)
                case "sraiw" => signExtend(newContext.reg(op1) >> op2, 32)
                case "jalr"  => newContext.pc + ConcVal(4)
                // case "jalr"  => Top(false)
                case "ecall" => throw new NotImplementedError 
                case "ebreak" => throw new NotImplementedError 
                case _ => throw new NotImplementedError 
            }
            newContext.reg(op0) = nval
            opcode match {
                case "jalr" => {
                    assert(newContext.reg(op1).isInstanceOf[ConcVal], s"${newContext.reg(op1).getClass}")
                    newContext.pc = newContext.reg(op1) + op2
                }
                case _ => {
                    updop = Some(PEvalInfo(InstIdOp(op1), InstIdOp("zero"), InstIdOp(op0), Top(true), a1, Top(true), nval))
                    newContext.pc = newContext.pc + ConcVal(4)
                }
            }
        }
        else if (jtype.contains(opcode)) {
            val op0 = inst.operands(0).asInstanceOf[InstIdOp].reg
            val op1 = ConcVal(inst.operands(1).asInstanceOf[InstImmOp].imm)
            assert(opcode == "jal")
            newContext.reg(op0) = newContext.pc + ConcVal(4)
            newContext.pc = op1
        }
        else if (btype.contains(opcode)) {
            val op0 = inst.operands(0).asInstanceOf[InstIdOp].reg
            val op1 = inst.operands(1).asInstanceOf[InstIdOp].reg
            val op2 = ConcVal(inst.operands(2).asInstanceOf[InstImmOp].imm)
            assert((newContext.reg(op0).isInstanceOf[ConcVal] && newContext.reg(op1).isInstanceOf[ConcVal]) ||
                   (newContext.reg(op0).isInstanceOf[Address] && newContext.reg(op1).isInstanceOf[Address]))
            if ((opcode match {
                case "beq" => newContext.reg(op0) == newContext.reg(op1)
                case "bne" => newContext.reg(op0) != newContext.reg(op1)
                case "blt" => newContext.reg(op0) < newContext.reg(op1)
                case "bge" => newContext.reg(op0) >= newContext.reg(op1)
                case "bltu" => newContext.reg(op0) :< newContext.reg(op1)
                case "bgeu" => newContext.reg(op0) :>= newContext.reg(op1)
                case _ => throw new NotImplementedError 
            }) == ConcVal(1)) {
                newContext.pc = op2
            } else {
                newContext.pc = newContext.pc + ConcVal(4)
            }
        }
        else if (utype.contains(opcode)) {
            val op0 = inst.operands(0).asInstanceOf[InstIdOp].reg
            val op1 = inst.operands(1).asInstanceOf[InstImmOp].imm
            val nval = opcode match {
                case "lui" => ConcVal(op1 << 12, false)
                case _ => throw new NotImplementedError 
            }
            updop = Some(PEvalInfo(InstIdOp("zero"), InstIdOp("zero"), InstIdOp(op0), Top(true), Top(true), Top(true), nval))
            newContext.reg(op0) = nval
            newContext.pc = newContext.pc + ConcVal(4)
            // throw new NotImplementedError
        }
        else if (mul.contains(opcode)) {
            val op0 = inst.operands(0).asInstanceOf[InstIdOp].reg
            val op1 = inst.operands(1).asInstanceOf[InstIdOp].reg
            val op2 = inst.operands(2).asInstanceOf[InstIdOp].reg

            val a1 = newContext.reg(op1)
            val a2 = newContext.reg(op2)
            val nval = opcode match {
                case "mul"  => newContext.reg(op1) * newContext.reg(op2)
                case "mulw" => signExtend(newContext.reg(op1) * newContext.reg(op2), 32)
                case _ => throw new NotImplementedError 
            }
            updop = Some(PEvalInfo(InstIdOp(op1), InstIdOp(op2), InstIdOp(op0), Top(true), a1, a2, nval))
            newContext.reg(op0) = nval
            newContext.pc = newContext.pc + ConcVal(4)
        }
        else if (opcode == "nop") {
            newContext.pc = newContext.pc + ConcVal(4)
        }
        else {
            throw new NotImplementedError(s"${opcode}")
        }
        newContext.reg("zero") = ConcVal(0)
        assert(newContext.pc.isInstanceOf[ConcVal], s"${newContext.pc.getClass}")
        // print update
        if (debug) {
            newContext.printReg()
            newContext.printStack()
        }
        (newContext, updop)
    }


    def getPaths(entryloc: InstPointer, targetloc: InstPointer, edges: List[(InstPointer, InstPointer, VIRUnroller.CFType)], depth: Int) : List[List[InstPointer]] = {
        var visitCount = Map[InstPointer, Int]().withDefaultValue(0)
        var paths = List[List[InstPointer]]()

        def dfs(curloc: InstPointer, path: List[InstPointer]) : Unit = {
            if (curloc == targetloc) {
                paths = path.reverse :: paths
                return
            }
            if (visitCount(curloc) >= depth) { return }
            visitCount(curloc) += 1
            val outedges = edges.filter(e => e._1 == curloc)
            outedges.map(e => {
                dfs(e._2, e._1 :: path)
            })
        }

        dfs(entryloc, List[InstPointer]())
        return paths
    }

    def rangesToContext (pc: Int, ranges: List[(Int, Int, Boolean)]) : TaintContext = {
        val rstack: Map[Address, AbsValue] = Map.empty ++ (ranges.flatMap{
            case r => List.range(r._1, r._2, 4).map(x => (Address(x), Top(r._3))).toSeq
        }).toMap

        val tc = TaintContext(pc=ConcVal(pc))
        tc.stack ++= rstack
        tc
    }

    def executeBlock (virab: VIRAtomicBlock, context: TaintContext) : List[(TaintContext, Option[PEvalInfo])] = {
        val pevals = virab.instructions.foldLeft[List[(TaintContext, Option[PEvalInfo])]](List((context, None)))(
            (acc, inst) => updateContext(inst, acc.head._1)::acc).reverse
        if (debug) println((pevals.tail zip virab.instructions).map(a => s"instruction ${a._2} with peval ${a._1._2}").mkString("\n"))
        pevals
    }

    def mergeContexts (contexts: List[(InstPointer, TaintContext)]): 
        scala.collection.immutable.Map[InstPointer, TaintContext] = {
        def mergeAbsValue(v1: AbsValue, v2: AbsValue) : AbsValue = (v1, v2) match {
            case (Top(true), _) => Top(true)
            case (_, Top(true)) => Top(true)
            case (ConcVal(_, true), _) => Top(true)
            case (_, ConcVal(_, true)) => Top(true)
            case (Address(_, true), _) => Top(true)
            case (_, Address(_, true)) => Top(true)
            case _ => Top(false)
        }
        def union(c1: TaintContext, c2: TaintContext) : TaintContext = {
            val merged = c1.copy()
            c2.reg.foreach{case (r, d) => {
                merged.reg(r) = mergeAbsValue(merged.reg(r), d)
            }}
            c2.stack.foreach{case (a, d) => {
                merged.stack(a) = mergeAbsValue(merged.stack(a), d)
            }}
            merged
        }

        val m = Map[InstPointer, TaintContext]()
        contexts.foreach{case (loc, ctx) => {
            m(loc) = if (m.contains(loc)) union(m(loc), ctx) else ctx
        }}
        scala.collection.immutable.Map(m.toSeq: _*)
    }

    def getTaintContexts (virp: VIRProgram, initcontext: TaintContext, budget: Int = 1000) : 
        scala.collection.immutable.Map[InstPointer, TaintContext] = {
        // recursive function, runs through each instruction in the block and 
        // adds context to a list

        // Sanity check that entry address is the same as initcontext
        assert(initcontext.pc match {
            case ConcVal(v, b) => v == virp.entryloc.loc
            case _ => false
        }, s"TaintContext and VIRProgram are inconsistent: ${virp.entryloc} != ${initcontext.pc}")

        def stepBlock (virab: VIRAtomicBlock, context: TaintContext) : (InstPointer, TaintContext) = {
            val newContext = virab.instructions.foldLeft(context)((acc, inst) => updateContext(inst, acc)._1)
            val nextloc = newContext.pc.asInstanceOf[ConcVal].v.toInt
            (InstPointer(nextloc), newContext)
            // if (nextloc == targetloc.loc) newContext else executeBlock(virp.getBlock(nextloc).get, newContext)
        }

        def runTaintAnalysis(loclst: List[InstPointer]): TaintContext = {
            loclst.foldLeft(initcontext)(
                (context, loc) => {
                    val virab = virp.getBlock(loc.loc).get
                    virab.instructions.foldLeft(context)(
                        (acc, inst) => updateContext(inst, acc)._1
                    )
                }
            )
        }

        mergeContexts((0 until budget).foldLeft((List[(InstPointer, TaintContext)]((virp.entryloc, initcontext))))(
            (acc, i) => {
                val nextloc = acc.head._1.loc
                if (nextloc == 0) acc
                else stepBlock(virp.getBlock(nextloc).get, acc.head._2)::acc
            }
        ))

        // val entryab = virp.getBlock(virp.entryloc.loc).get
        // val context = executeBlock(entryab, setTaint(TaintContext(pc=ConcVal(virp.entryloc.loc)), high))
        // List(context)
        // val contexts = getPaths(virp.entryloc, targetloc, VIRUnroller.getEdges(virp), depth).map(loclst => runTaintAnalysis(loclst))
        // contexts.reverse
    }


    def performAnalysis (virp: VIRProgram, itcstring: String, budget: Int) : 
        scala.collection.immutable.Map[Int, String] = {
        // Read in the file context into a string
        val inittc = TaintContextJSON.parseJSON(itcstring)
        // Run taint analysis
        getTaintContexts(virp, inittc._2, budget).map(entry => (entry._1.loc, 
            TaintContextJSON.createJson(inittc._1, entry._2))).toMap
    }
}