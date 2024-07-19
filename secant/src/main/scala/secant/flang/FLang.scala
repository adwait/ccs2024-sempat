/*
 * SemPat Project.
 * 
 * @file Flang.scala
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
 * FLang AST Classes.
 *
 */

package secant
package flang

import scala.collection.mutable.ListBuffer
import scala.collection.mutable.Stack

object FLang {
    def UInt(i: Int) = FIntLit(i)
    def zero = UInt(0)
    def one = UInt(1)
    def trueLit = FBoolLit(true)
    def falseLit = FBoolLit(false)
    def bv(i: BigInt, width: Int) = {
        (i < 0) match {
            case true => FBVLit((BigInt(1) << width) + i, width)
            case false => FBVLit(i, width)
        }
    }

    def integert = FIntType()
    def booleant = FBoolType()
    def bvt (width: Int) = FBitVectorType(width)
    def ut (name: String) = FUninterpretedType(name)
    def arrayt (indexType: FType, elemType: FType) = FArrayType(indexType, elemType)

    def when (cond: FExpr) (stmt: FStmt*) : FIfStmt = FIfStmt(cond, FBlock(stmt.toList))
    def skip () : FStmt = FSkip()
    def ite (cond: FExpr, texpr: FExpr, eexpr: FExpr) : FITEExpr = FITEExpr(cond, texpr, eexpr)
    def havoc (v: FStateVar) : FHavoc = FHavoc(v)

    def block (stmts: FStmt*) : FBlock = FBlock(stmts.toList)

    def isOpExprValidLHS (e: FOpExpr) : Boolean = {
        e.op match {
            case FBVExtract(he, le) => true
            case FArrayIndex(e) => true
            case _ => return false
        }
    }

    def rewriteExpr (e : FExpr, paramRewriter : FStateVar => FStateVar) : FExpr = {
        e match {
            case FOpExpr(op, args) => op match {
                case FArrayIndex(e) => 
                    FOpExpr(FArrayIndex(rewriteExpr(e, paramRewriter)), args.map((a: FExpr) => rewriteExpr(a, paramRewriter)))
                case FBVExtract(he, le) => 
                    FOpExpr(FBVExtract(rewriteExpr(he, paramRewriter), rewriteExpr(le, paramRewriter)), args.map((a: FExpr) => rewriteExpr(a, paramRewriter)))
                case _ => FOpExpr(op, args.map((a: FExpr) => rewriteExpr(a, paramRewriter)))
            }
            case FIntLit(i) => FIntLit(i)
            case FFuncInvocation(id, args) => FFuncInvocation(id, args.map((a: FExpr) => rewriteExpr(a, paramRewriter)))
            case FBVLit(v, w) => FBVLit(v, w)
            case FITEExpr(cond, thn, els) => FITEExpr(rewriteExpr(cond, paramRewriter), rewriteExpr(thn, paramRewriter), rewriteExpr(els, paramRewriter))
            case (s : FStateVar) => paramRewriter(s)
            case FId(id) => FId(id)
            case FBoolLit(b) => FBoolLit(b)
            case _ => throw new Exception("Unknown expression type")
        }
    }

    def rewriteStmt (s: FStmt, paramRewriter: FStateVar => FStateVar) : FStmt = {
        s match {
            case FAssignStmt(lhs, rhs) => FAssignStmt(rewriteExpr(lhs, paramRewriter), rewriteExpr(rhs, paramRewriter))
            case FBlock(body) => FBlock(body.map((s: FStmt) => rewriteStmt(s, paramRewriter)))
            case FIfElseStmt(cond, thenStmt, elseStmt) => FIfElseStmt(rewriteExpr(cond, paramRewriter), rewriteStmt(thenStmt, paramRewriter), rewriteStmt(elseStmt, paramRewriter))
            case FIfStmt(cond, thenStmt) => FIfStmt(rewriteExpr(cond, paramRewriter), rewriteStmt(thenStmt, paramRewriter))
            case FHavoc(v) => FHavoc(paramRewriter(v))
            case FSkip() => FSkip()
            case FAssume(cond) => FAssume(rewriteExpr(cond, paramRewriter))
        }
    }

    def hardenParam (p: FStateVar) : FStateVar = {
        p match {
            case FGlobalParam(id, typ) =>  FVar(id, typ)
            case FLocalParam(id, typ) => FVar(id, typ)
            case FVar(id, typ) => FVar(id, typ)
            case FLabeledVar(id, typ, lab) => FLabeledVar(id, typ, lab)
        }
    }
    def rewriteHardenExpr (e: FExpr) : FExpr = rewriteExpr(e, hardenParam)
    def rewriteHardenStmt (s: FStmt) : FStmt = rewriteStmt(s, hardenParam)
}

sealed abstract class FStmt
abstract class AuxilliaryStmt

abstract trait FDecl {
    override def toString(): String = ???
}


case class FBlock (body: List[FStmt]) extends FStmt {
    override def toString(): String = body.toString()
}
case class FAssignStmt (lhs: FExpr, rhs: FExpr) extends FStmt {
    override def toString(): String = s"${lhs.toString()} := ${rhs.toString()}"
}
case class FIfStmt (cond: FExpr, thenStmt: FStmt) extends FStmt {
    override def toString(): String = s"if (${cond.toString()}) {\n${thenStmt}\n}"
    def otherwise (stmts: FStmt*) : FStmt = FIfElseStmt(cond, thenStmt, FBlock(stmts.toList))
}
case class FIfElseStmt (cond: FExpr, thenStmt: FStmt, elseStmt: FStmt) extends FStmt {
    override def toString(): String = s"if (${cond.toString()}) {\n${thenStmt}\n} else {\n${elseStmt.toString()}\n}"
}
case class FSkip() extends FStmt {
    override def toString(): String = "skip"
}
case class FHavoc(v: FStateVar) extends FStmt {
    override def toString(): String = s"havoc (${v.toString()})"
}
case class FAssume(cond: FExpr) extends FStmt {
    override def toString(): String = s"assume (${cond.toString()})"
}

sealed abstract class FType

case class FIntType() extends FType {
    override def toString(): String = "int"
}
case class FBoolType() extends FType {
    override def toString(): String = "bool"
}
case class FBitVectorType(width: Int) extends FType {
    override def toString(): String = s"bv${width}"
}
case class FUninterpretedType(name: String) extends FType {
    override def toString(): String = name
}
case class FArrayType(indexType: FType, elemType: FType) extends FType {
    override def toString(): String = s"array[${indexType.toString()}] of ${elemType.toString()}"
}

sealed abstract class FFunc extends FDecl {
    override def toString(): String = ???
    def id: String = ???

    def apply(args: FExpr*) = FFuncInvocation(this, args.toList)
}
case class FUFunc(override val id: String, inp: List[FType], out: FType) extends FFunc {
    override def toString(): String = {
        val inpStr = inp.map(_.toString()).mkString(", ")
        s"uninterpreted function $id($inpStr) : ${out.toString()}"
    }
}
case class FDefine(override val id: String, args: List[Tuple2[FId, FType]], out: FType, body: List[FExpr] => FExpr) extends FFunc {
    override def toString(): String = {
        val argStr = args.map(a => s"${a._1.toString()}: ${a._2.toString()}").mkString(", ")
        s"define $id($argStr) = ${body(args.map(a => a._1)).toString()}"
    }
}


sealed abstract class FPolyOp {
    override def toString(): String = ???
}
// Arithmetic
case class FPlus() extends FPolyOp {
    override def toString(): String = "+"
}
case class FMinus() extends FPolyOp {
    override def toString(): String = "-"
}
// Bitwise
case class FBVShiftRight() extends FPolyOp {
    override def toString(): String = ">>"
}
case class FBVShiftLeft() extends FPolyOp {
    override def toString(): String = "<<"
}
case class FBVAnd() extends FPolyOp {
    override def toString(): String = "&"
}
case class FBVOr() extends FPolyOp {
    override def toString(): String = "|"
}
case class FBVXor() extends FPolyOp {
    override def toString(): String = "^"
}
case class FBVExtract(he: FExpr, le: FExpr) extends FPolyOp {
    override def toString(): String = s"[(${he.toString()}):(${le.toString()})]"
}
case class FBVConcat() extends FPolyOp {
    override def toString(): String = "++"
}
// Comparison
case class FEq() extends FPolyOp {
    override def toString(): String = "=="
}
case class FNeq() extends FPolyOp {
    override def toString(): String = "!="
}
case class FLt() extends FPolyOp {
    override def toString(): String = "<"
}
case class FLte() extends FPolyOp {
    override def toString(): String = "<="
}
case class FGt() extends FPolyOp {
    override def toString(): String = ">"
}
case class FGte() extends FPolyOp {
    override def toString(): String = ">="
}
// Boolean
case class FAnd() extends FPolyOp {
    override def toString(): String = "&&"
}
case class FOr() extends FPolyOp {
    override def toString(): String = "||"
}
case class FNot() extends FPolyOp {
    override def toString(): String = "!"
}
case class FImplies() extends FPolyOp {
    override def toString(): String = "==>"
}
case class FIff() extends FPolyOp {
    override def toString(): String = "<==>"
}
// Array indexing
case class FArrayIndex(e: FExpr) extends FPolyOp {
    override def toString(): String = s"[${e.toString()}]"
}
// Function invocation
case class FFuncInvocation(id: FFunc, args: List[FExpr]) extends FExpr {
    override def toString(): String = {
        val argStr = args.map(_.toString()).mkString(", ")
        s"$id($argStr)"
    }
}

sealed abstract class FExpr {
    def +(e: FExpr) = FOpExpr(FPlus(), List(this, e))
    def -(e: FExpr) = FOpExpr(FMinus(), List(this, e))
    
    def >>(e: FExpr) = FOpExpr(FBVShiftRight(), List(this, e))
    def <<(e: FExpr) = FOpExpr(FBVShiftLeft(), List(this, e))
    def &(e: FExpr) = FOpExpr(FBVAnd(), List(this, e))
    def |(e: FExpr) = FOpExpr(FBVOr(), List(this, e))
    def ^(e: FExpr) = FOpExpr(FBVXor(), List(this, e))
    def ++(e: FExpr) = FOpExpr(FBVConcat(), List(this, e))

    def <(e: FExpr) = FOpExpr(FLt(), List(this, e))
    def <=(e: FExpr) = FOpExpr(FLte(), List(this, e))
    def >(e: FExpr) = FOpExpr(FGt(), List(this, e))
    def >=(e: FExpr) = FOpExpr(FGte(), List(this, e))
    def ===(e: FExpr) = FOpExpr(FEq(), List(this, e))
    def !==(e: FExpr) = FOpExpr(FNeq(), List(this, e))

    def &&(e: FExpr) = FOpExpr(FAnd(), List(this, e))
    def ||(e: FExpr) = FOpExpr(FOr(), List(this, e))
    def unary_!() = FOpExpr(FNot(), List(this))
    def ==> (e: FExpr) = FOpExpr(FImplies(), List(this, e))
    def <==> (e: FExpr) = FOpExpr(FIff(), List(this, e))
    def apply(h: FExpr, l: FExpr) = FOpExpr(FBVExtract(h, l), List(this))

    def apply(e: FExpr) = FOpExpr(FArrayIndex(e), List(this))

    def :=(e: FExpr) = FAssignStmt(this, e)

    override def toString(): String = ???
}
case class FId(id: String) extends FExpr {
    override def toString(): String = id
}
sealed abstract class FStateVar(id: String, typ: FType) extends FExpr with FDecl {
    val isHardened : Boolean = false
}
case class FVar(id: String, typ: FType) extends FStateVar(id, typ) {
    override def toString(): String = id
    override val isHardened: Boolean = true
}
case class FLabeledVar(id: String, typ: FType, lab: Int) extends FStateVar(id, typ) {
    override def toString(): String = s"${id}_${lab}"
}
sealed abstract class FParam(id: String, typ: FType) extends FStateVar(id, typ)
case class FLocalParam(id: String, typ: FType) extends FParam(id, typ) {
    override def toString(): String = id
}
case class FGlobalParam(id: String, typ: FType) extends FParam(id, typ) {
    override def toString(): String = id
}
sealed abstract class FLit extends FExpr
sealed abstract class FNLit extends FExpr
case class FIntLit(i: Integer) extends FNLit {
    override def toString(): String = i.toString()
}
case class FBoolLit(b: Boolean) extends FLit {
    override def toString(): String = b.toString()
}
case class FBVLit(v: BigInt, w: Int) extends FNLit {
    override def toString(): String = s"0x${v.toString(16)}"
}
case class FOpExpr(op: FPolyOp, args: List[FExpr]) extends FExpr {
    override def toString(): String = {
        val argStr = args.map(_.toString()).mkString(", ")
        s"${op.toString()}($argStr)"
    }
}
case class FITEExpr (cond: FExpr, thn: FExpr, els: FExpr) extends FExpr {
    override def toString(): String = {
        s"if (${cond.toString()}) then (${thn.toString()}) else (${els.toString()})"
    }
}
case class FForall (fvar: FId, ftyp: FType, body: FExpr) extends FExpr {
    override def toString(): String = {
        s"forall ($fvar : $ftyp) ${body.toString()}"
    }
}
case class FExists (fvar: FId, ftyp: FType, body: FExpr) extends FExpr {
    override def toString(): String = {
        s"exists ($fvar : $ftyp) ${body.toString()}"
    }
}