/*
 * SemPat Project.
 * 
 * @file Utils.scala
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

import secant.flang.FLang._
import secant.flang._

object Utils {
    // Expand local parameter with micro-instruction id
    def labMopToString (lab: Int, mop: MicroOp) = s"mi_${lab}_${mop}"
    def expandLocalParam (p: FLocalParam, lab: Int, mop: MicroOp) = s"${labMopToString(lab, mop)}_param_${p.id}"
    def labelLocalParam (p: FLocalParam, lab: Int, mop: MicroOp) : FLabeledVar = {
        FLabeledVar(s"${mop}_param_${p.id}", p.typ, lab)
    }
    def llp (p: FLocalParam, lab: Int, mop: MicroOp) = labelLocalParam (p, lab, mop)
    def hardenLabeledVarExpr (expr: FExpr, indexMap: Map[Int, Int] = Map().withDefault(a => a)) : FExpr = 
        rewriteExpr(expr, (p: FStateVar) => p match {
            case FLabeledVar(id, typ, lab) => FVar(s"mi_${indexMap(lab)}_${id}", typ)
            case _ => {
                SemPatDriver.ERROR(s"Unexpected state variable ${p} of class ${p.getClass()} in tableauMatchesAt. Tableau predicates are defined over FLabeledVar. Aborting...")
                throw new Exception("Unexpected state variable in tableauMatchesAt.")
            }
        })

    def mkHardenedStmtCopy (exec: FStmt, cpy: Int) = {
        FLang.rewriteStmt(exec, (p: FStateVar) => p match {
            case p: FVar => FVar(getCopy(p.id, cpy), p.typ)
            case _ => {
                SemPatDriver.ERROR(s"Unexpected FStateVar ${p} of class ${p.getClass()} in mkStmtCopy. Everything must be hardened to FVars by now. Aborting...")
                throw new Exception("Unexpected state variable in mkHardenedStmtCopy.")
            }
        })
    }

    def mkHardenedExprCopy (expr: FExpr, cpy: Int) = {
        FLang.rewriteExpr(expr, (p: FStateVar) => p match {
            case p: FVar => FVar(getCopy(p.id, cpy), p.typ)
            case _ => {
                SemPatDriver.ERROR(s"Unexpected FStateVar ${p} of class ${p.getClass()} in mkExprCopy. Everything must be hardened to FVars by now. Aborting...")
                throw new Exception("Unexpected state variable in mkHardenedExprCopy.")
            }
        })
    }

    // Get the name of the ith copy
    def getCopy (s: String, i: Int) = s + "_copy" + i.toString()
}

