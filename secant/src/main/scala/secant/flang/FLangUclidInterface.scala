/*
 * SemPat Project.
 * 
 * @file FLangUclidInterface.scala
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
 * Compiler from FLang programs to the UCLID Model Checking Language.
 *
 */

package secant.flang

import uclid.lang.Decl
import uclid.lang.Expr
import uclid.lang.ITEOp
import uclid.lang.Lhs
import uclid.lang.Identifier
import uclid.lang.VarBitVectorSlice
import uclid.lang.BlockStmt
import uclid.lang.InitDecl
import uclid.lang.NumericLit
import uclid.lang.HavocableEntity
import uclid.lang.HavocableId

object FLangUclidInterface {

    def intVar (name: String) : Decl = {
        uclid.lang.StateVarsDecl(List(uclid.lang.Identifier(name)), uclid.lang.IntegerType())
    }
    def boolVar (name: String) : Decl = {
        uclid.lang.StateVarsDecl(List(uclid.lang.Identifier(name)), uclid.lang.BooleanType())
    }
    def bvVar (name: String, width: Int) : Decl = {
        uclid.lang.StateVarsDecl(List(uclid.lang.Identifier(name)), uclid.lang.BitVectorType(width))
    }
    def iden (name: String) : Identifier = {
        uclid.lang.Identifier(name)
    }
    def ublock (stmts: List[uclid.lang.Statement]) : BlockStmt = {
        uclid.lang.BlockStmt(List(), stmts)
    }

    def init (stmts: List[uclid.lang.Statement] = List()) : InitDecl = {
        uclid.lang.InitDecl(uclid.lang.BlockStmt(List(), stmts))
    }

    def addOp (a: Expr, b: Expr) : Expr = {
        uclid.lang.OperatorApplication(uclid.lang.AddOp(), List(a, b))
    }
    def subOp (a: Expr, b: Expr) : Expr = {
        uclid.lang.OperatorApplication(uclid.lang.SubOp(), List(a, b))
    }
    def ltOp (a: Expr, b: Expr) : Expr = {
        uclid.lang.OperatorApplication(uclid.lang.LTOp(), List(a, b))
    }
    def leOp (a: Expr, b: Expr) : Expr = {
        uclid.lang.OperatorApplication(uclid.lang.LEOp(), List(a, b))
    }
    def gtOp (a: Expr, b: Expr) : Expr = {
        uclid.lang.OperatorApplication(uclid.lang.GTOp(), List(a, b))
    }
    def geOp (a: Expr, b: Expr) : Expr = {
        uclid.lang.OperatorApplication(uclid.lang.GEOp(), List(a, b))
    }
    def eqOp (a: Expr, b: Expr) : Expr = {
        uclid.lang.OperatorApplication(uclid.lang.EqualityOp(), List(a, b))
    }
    def neqOp (a: Expr, b: Expr) : Expr = {
        uclid.lang.OperatorApplication(uclid.lang.InequalityOp(), List(a, b))
    }
    def andOp (a: Expr*) : Expr = {
        uclid.lang.OperatorApplication(uclid.lang.ConjunctionOp(), a.toList)
    }
    def orOp (a: Expr*) : Expr = {
        uclid.lang.OperatorApplication(uclid.lang.DisjunctionOp(), a.toList)
    }
    def notOp (a: Expr) : Expr = {
        uclid.lang.OperatorApplication(uclid.lang.NegationOp(), List(a))
    }
    def impliesOp (a: Expr, b: Expr) : Expr = {
        uclid.lang.OperatorApplication(uclid.lang.ImplicationOp(), List(a, b))
    }
    def iffOp (a: Expr, b: Expr) : Expr = {
        uclid.lang.OperatorApplication(uclid.lang.IffOp(), List(a, b))
    }
    def iteOp (a: Expr, b: Expr, c: Expr) : Expr = {
        uclid.lang.OperatorApplication(uclid.lang.ITEOp(), List(a, b, c))
    }

    def FtoUclidType (typ: FType) : uclid.lang.Type = {
        typ match {
            case FIntType() => uclid.lang.IntegerType()
            case FBoolType() => uclid.lang.BooleanType()
            case FBitVectorType(w) => uclid.lang.BitVectorType(w)
            case FArrayType(indexType, elemType) => uclid.lang.ArrayType(List(FtoUclidType(indexType)), FtoUclidType(elemType))
            case FUninterpretedType(id) => uclid.lang.UninterpretedType(uclid.lang.Identifier(id))
        }
    }

    def FtoUclidId (id: FId) : uclid.lang.Identifier = { uclid.lang.Identifier(id.id) }

    def FtoUclidNumericLit (flit: FNLit) : NumericLit = {
        flit match {
            case FIntLit(v) => uclid.lang.IntLit(v.toLong)
            case FBVLit(v, w) => uclid.lang.BitVectorLit(v, w)
        }
    }

    def FtoUclidExpr (ex: FExpr) : Expr = {
        ex match {
            case FBVLit(v, w) => FtoUclidNumericLit(FBVLit(v, w))
            case FIntLit(v) => FtoUclidNumericLit(FIntLit(v))
            case FBoolLit(v) => uclid.lang.BoolLit(v)
            case FId(v) => uclid.lang.Identifier(v)
            case FVar(v, typ) => uclid.lang.Identifier(v)
            case FLabeledVar(id, typ, lab) => uclid.lang.Identifier(id)
            case FLocalParam(id, typ) => uclid.lang.Identifier(id)
            case FGlobalParam(id, typ) => uclid.lang.Identifier(id)
            case FITEExpr(c, t, e) => uclid.lang.OperatorApplication(ITEOp(), List(FtoUclidExpr(c), FtoUclidExpr(t), FtoUclidExpr(e)))
            case FFuncInvocation(id, args) => uclid.lang.FuncApplication(uclid.lang.Identifier(id.id), args.map(FtoUclidExpr))
            case FForall(fid, ftyp, body) =>  uclid.lang.OperatorApplication(
                uclid.lang.ForallOp(List((FtoUclidId(fid), FtoUclidType(ftyp))), List.empty), List(FtoUclidExpr(body)))
            case FExists(fid, ftyp, body) =>  uclid.lang.OperatorApplication(
                uclid.lang.ExistsOp(List((FtoUclidId(fid), FtoUclidType(ftyp))), List.empty), List(FtoUclidExpr(body)))
            case FOpExpr(op, args) => {
                val uclidOp = op match {
                    case FPlus() => uclid.lang.AddOp()
                    case FMinus() => uclid.lang.SubOp()
                    case FBVAnd() => uclid.lang.BVAndOp(0)
                    case FBVOr() => uclid.lang.BVOrOp(0)
                    case FBVXor() => uclid.lang.BVXorOp(0)
                    case FBVShiftLeft() => uclid.lang.BVLeftShiftBVOp(0)
                    case FBVShiftRight() => uclid.lang.BVLRightShiftBVOp(0)
                    case FBVExtract(h, l) => uclid.lang.VarExtractOp(uclid.lang.VarBitVectorSlice(FtoUclidExpr(h), FtoUclidExpr(l)))
                    case FBVConcat() => uclid.lang.ConcatOp()
                    case FEq() => uclid.lang.EqualityOp()
                    case FNeq() => uclid.lang.InequalityOp()
                    case FLt() => uclid.lang.LTOp()
                    case FLte() => uclid.lang.LEOp()
                    case FGt() => uclid.lang.GTOp()
                    case FGte() => uclid.lang.GEOp()
                    case FNot() => uclid.lang.NegationOp()
                    case FAnd() => uclid.lang.ConjunctionOp()
                    case FOr() => uclid.lang.DisjunctionOp()
                    case FImplies() => uclid.lang.ImplicationOp()
                    case FIff() => uclid.lang.IffOp()
                    case FArrayIndex(e) => uclid.lang.ArraySelect(List(FtoUclidExpr(e)))
                }
                uclid.lang.OperatorApplication(uclidOp, args.map(FtoUclidExpr))
            }
        }
    }

    def FtoUclidStmt (stmt : FStmt) : uclid.lang.Statement = {
        stmt match {
            case FAssignStmt(lhs, rhs) => lhs match {
                case FId(id) => uclid.lang.AssignStmt(List(uclid.lang.LhsId(iden(id))), List(FtoUclidExpr(rhs)))
                case FVar(id, _) => uclid.lang.AssignStmt(List(uclid.lang.LhsId(iden(id))), List(FtoUclidExpr(rhs)))
                case FLabeledVar(id, _, _) => uclid.lang.AssignStmt(List(uclid.lang.LhsId(iden(id))), List(FtoUclidExpr(rhs)))
                case FLocalParam(id, _) => uclid.lang.AssignStmt(List(uclid.lang.LhsId(iden(id))), List(FtoUclidExpr(rhs)))
                case FGlobalParam(id, _) => uclid.lang.AssignStmt(List(uclid.lang.LhsId(iden(id))), List(FtoUclidExpr(rhs)))
                case FOpExpr(FBVExtract(h, l), List(p)) => p match {
                    case FId(id) => uclid.lang.AssignStmt(List(uclid.lang.LhsVarSliceSelect(iden(id), VarBitVectorSlice(FtoUclidExpr(h), FtoUclidExpr(l)))), List(FtoUclidExpr(rhs)))
                    case FVar(id, typ) => uclid.lang.AssignStmt(List(uclid.lang.LhsVarSliceSelect(iden(id), VarBitVectorSlice(FtoUclidExpr(h), FtoUclidExpr(l)))), List(FtoUclidExpr(rhs)))
                    case FLabeledVar(id, typ, lab) => uclid.lang.AssignStmt(List(uclid.lang.LhsVarSliceSelect(iden(id), VarBitVectorSlice(FtoUclidExpr(h), FtoUclidExpr(l)))), List(FtoUclidExpr(rhs)))
                    case FLocalParam(id, typ) => uclid.lang.AssignStmt(List(uclid.lang.LhsVarSliceSelect(iden(id), VarBitVectorSlice(FtoUclidExpr(h), FtoUclidExpr(l)))), List(FtoUclidExpr(rhs)))
                    case FGlobalParam(id, typ) => uclid.lang.AssignStmt(List(uclid.lang.LhsVarSliceSelect(iden(id), VarBitVectorSlice(FtoUclidExpr(h), FtoUclidExpr(l)))), List(FtoUclidExpr(rhs)))
                    case _ => throw new Exception(s"Invalid LHS: $lhs")        
                }
                case FOpExpr(FArrayIndex(e), List(p)) => p match {
                    case FId(id) => uclid.lang.AssignStmt(List(uclid.lang.LhsArraySelect(iden(id), List(FtoUclidExpr(e)))), List(FtoUclidExpr(rhs)))
                    case FVar(id, typ) => uclid.lang.AssignStmt(List(uclid.lang.LhsArraySelect(iden(id), List(FtoUclidExpr(e)))), List(FtoUclidExpr(rhs)))
                    case FLabeledVar(id, typ, lab) => uclid.lang.AssignStmt(List(uclid.lang.LhsArraySelect(iden(id), List(FtoUclidExpr(e)))), List(FtoUclidExpr(rhs)))
                    case FLocalParam(id, typ) => uclid.lang.AssignStmt(List(uclid.lang.LhsArraySelect(iden(id), List(FtoUclidExpr(e)))), List(FtoUclidExpr(rhs)))
                    case FGlobalParam(id, typ) => uclid.lang.AssignStmt(List(uclid.lang.LhsArraySelect(iden(id), List(FtoUclidExpr(e)))), List(FtoUclidExpr(rhs)))
                    // case FOpExpr(FArrayIndex(e1), List(p1)) => p1 match {
                    //     case FId(id1) => uclid.lang.AssignStmt(List(uclid.lang.LhsArraySelect(iden(id1), List(FtoUclidExpr(e1), FtoUclidExpr(e)))), List(FtoUclidExpr(rhs)))
                    //     case FVar(id1, typ1) => uclid.lang.AssignStmt(List(uclid.lang.LhsArraySelect(iden(id1), List(FtoUclidExpr(e1), FtoUclidExpr(e)))), List(FtoUclidExpr(rhs)))
                    //     case FLabeledVar(id1, typ1, lab1) => uclid.lang.AssignStmt(List(uclid.lang.LhsArraySelect(iden(id1), List(FtoUclidExpr(e1), FtoUclidExpr(e)))), List(FtoUclidExpr(rhs)))
                    //     case FLocalParam(id1, typ1) => uclid.lang.AssignStmt(List(uclid.lang.LhsArraySelect(iden(id1), List(FtoUclidExpr(e1), FtoUclidExpr(e)))), List(FtoUclidExpr(rhs)))
                    //     case FGlobalParam(id1, typ1) => uclid.lang.AssignStmt(List(uclid.lang.LhsArraySelect(iden(id1), List(FtoUclidExpr(e1), FtoUclidExpr(e)))), List(FtoUclidExpr(rhs)))
                    //     case _ => throw new Exception(s"Invalid LHS: $lhs")        
                    // }
                    case _ => throw new Exception(s"Invalid LHS: $lhs")        
                }
                case _ => throw new Exception(s"Invalid LHS: $lhs")
            }
            case FIfStmt(c, t) => uclid.lang.IfElseStmt(FtoUclidExpr(c), FtoUclidStmt(t), ublock(List()))
            case FIfElseStmt(c, t, e) => uclid.lang.IfElseStmt(FtoUclidExpr(c), FtoUclidStmt(t), FtoUclidStmt(e))
            case FBlock(b) => ublock(b.map(s => FtoUclidStmt(s)))
            case FHavoc(v) => v match {
                case FLabeledVar(id, typ, lab) => uclid.lang.HavocStmt(HavocableId(iden(id)))
                case FGlobalParam(id, typ) => uclid.lang.HavocStmt(HavocableId(iden(id)))
                case FLocalParam(id, typ) => uclid.lang.HavocStmt(HavocableId(iden(id)))
                case FVar(id, typ) => uclid.lang.HavocStmt(HavocableId(iden(id)))
            }
            case FSkip() => uclid.lang.SkipStmt()
            case FAssume(cond) => uclid.lang.AssumeStmt(FtoUclidExpr(cond), None)
        }
    }

}