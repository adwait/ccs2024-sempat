/*
 * SemPat Project.
 * 
 * @file MicroProgram.scala
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

import secant.flang._
import virparser.VIRAtomicBlock
import virparser.VIRInstruction
import virparser.{TaintContext, PEvalInfo}

/**
  * A MicroOp is a single microcode operation.
  * It can have a (functional) global state behavior.
  * 
  * This file defines some sample microops.
  * These do not have any functional behavior.
  */
abstract class MicroOp {
    def functional : Map[MicroStage, FStmt] = Map()
    def parameters : List[FLocalParam] = List()
    def >>>(st: MicroStage) = OpPath(this, List(st))
}
trait HasCondition {
    def condition : FExpr
}
trait HasArchFunctional {
    def archfunctional : Map[MicroStage, FStmt]
}

abstract class BranchOp extends MicroOp with HasCondition

sealed abstract class MicroProgram {
    def labelProgram (ctr: Int) : Tuple2[LabeledMicroProgram, Int] = {
        this match {
            case a: MicroInstr => (LabeledMicroInstr(ctr, a.mop, a.fields), ctr+1)
            case MicroSequence(ops) => {
                val (labeledOps, ctrnew) = ops.foldLeft((List[LabeledMicroProgram](), ctr))((acc, op) => {
                    val (labeledOp, ctr2) = op.labelProgram(acc._2)
                    (acc._1 :+ labeledOp, ctr2)
                })
                (LabeledMicroSequence(labeledOps), ctrnew)
            }
            case MicroBranch(cond, thenBranch, elseBranch, f) => {
                val ctr2 = ctr + 1
                val (labeledThenBranch, ctr3) = thenBranch.labelProgram(ctr2)
                val (labeledElseBranch, ctr4) = elseBranch.labelProgram(ctr3)
                (LabeledMicroBranch(ctr, cond, labeledThenBranch, labeledElseBranch, f), ctr3)
            }
        }
    }

    def getLabeledProgram () : LabeledMicroProgram = labelProgram(0)._1
}
object MicroProgram {
    type VIRABCompiler = (VIRInstruction, Option[PEvalInfo]) => LabeledMicroInstr

    def branch (cond: BranchOp, thenBranch: MicroProgram, elseBranch: MicroProgram) : MicroProgram = MicroBranch(cond, thenBranch, elseBranch)
    
    // Make labelled program with parameters
    def seqToLabeledProgram (a: (Tuple2[MicroOp, ParamAnnotationMap])*) : LabeledMicroProgram = MicroSequence(a.toList.map(t => MicroInstr(t._1, t._2))).getLabeledProgram()
    def lseqToLabeledProgram (a: LabeledMicroInstr*) : LabeledMicroProgram = LabeledMicroSequence(a.toList)

    def VIRAtomicBlockToLabeledProgram (vira: VIRAtomicBlock, comp: VIRABCompiler, tcs: List[Option[PEvalInfo]]) : LabeledMicroProgram = {
        LabeledMicroSequence((vira.instructions zip tcs).map(a => comp(a._1, a._2)))
    }

    type LMOP = (Int, MicroOp)

    // Add annotations to instruction parameters
    sealed abstract class ParamAnnotation
    sealed abstract class InstrOperand extends ParamAnnotation
    case class InstrOperandValue (v: FNLit) extends InstrOperand
    case class InstrOperandSymb () extends InstrOperand
    case class RuntimeParam () extends ParamAnnotation
    case class RuntimePEval (v: FNLit, spec: Option[FExpr]) extends ParamAnnotation

    def instopv (v: FNLit) : ParamAnnotation = InstrOperandValue(v)
    def instops () : ParamAnnotation = InstrOperandSymb()
    def runtimep () : ParamAnnotation = RuntimeParam()
    def runtimepeval (v: FNLit) : ParamAnnotation = RuntimePEval(v, None)
    def runtimepeval (v: FNLit, spec_expr: FExpr) : ParamAnnotation = RuntimePEval(v, Some(spec_expr))

    type ParamAnnotationMap = Map[FLocalParam, ParamAnnotation]
    def mkParamMap (a: List[(FLocalParam, ParamAnnotation)] = List()) : ParamAnnotationMap = Map(a: _*).withDefault(_ => instops())
    // Empty parameter map
    val EPM = mkParamMap()
}
case class MicroInstr (mop: MicroOp, fields: MicroProgram.ParamAnnotationMap = MicroProgram.mkParamMap()) extends MicroProgram
case class MicroSequence (ops : List[MicroProgram]) extends MicroProgram
case class MicroBranch (cond : BranchOp, thenBranch : MicroProgram, elseBranch : MicroProgram, fields: MicroProgram.ParamAnnotationMap = MicroProgram.mkParamMap()) extends MicroProgram


sealed abstract class LabeledMicroProgram
case class LabeledMicroInstr (lab: Int, mop: MicroOp, fields : MicroProgram.ParamAnnotationMap = MicroProgram.mkParamMap()) extends LabeledMicroProgram {
    override def toString () : String = {
        s"LabeledMicroInstr($lab,$mop,$fields)"
    }
}
case class LabeledMicroBranch (lab: Int, cond : BranchOp, thenBranch : LabeledMicroProgram, elseBranch : LabeledMicroProgram, 
    fields: MicroProgram.ParamAnnotationMap = MicroProgram.mkParamMap()) extends LabeledMicroProgram {
    
    override def toString () : String = {
        s"$lab: if (${cond}) {\n$thenBranch\n}\nelse {\n$elseBranch\n}"
    }
}
case class LabeledMicroSequence (ops : List[LabeledMicroProgram]) extends LabeledMicroProgram {
    def isStraightLine () : Boolean = {
        ops.forall(op => op match {
            case LabeledMicroInstr(_, _, _) => true
            case _ => false
        })
    }
    override def toString () : String = {
        ops.map(_.toString()).mkString("\n")
    }
}


