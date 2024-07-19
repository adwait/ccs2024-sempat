package secant
package flang

import FLang._

object FLangAnalyzer {

    type ModSummary = Map[FExpr, List[FStateVar]]

    val use_expr_cache = scala.collection.mutable.HashMap[FExpr, List[FStateVar]]()
    val use_cache = scala.collection.mutable.HashMap[FStmt, List[FStateVar]]()
    val mod_cache = scala.collection.mutable.HashMap[FStmt, List[FStateVar]]()
    val trace_cache = scala.collection.mutable.HashMap[(FStmt, FStateVar), List[FStateVar]]()

    def clearCache () = {
        use_expr_cache.clear()
        use_cache.clear()
        mod_cache.clear()
        trace_cache.clear()
        use_cache(FSkip()) = List()
    }

    def modifiesState (fstmt: FStmt) : List[FStateVar] = {
        clearCache()
        _modifiesState(fstmt)
    }

    def _modifiesState (fstmt: FStmt) : List[FStateVar] = {
        if (mod_cache.contains(fstmt)) return mod_cache(fstmt)
        val mods = (fstmt match {
            case FAssignStmt(lhs, rhs) => lhs match {
                case a: FParam => List(a)
                case a: FVar => List(a)
                case e: FOpExpr => isOpExprValidLHS(e) match {
                    case true => e.args match {
                        case List(a: FParam) => List(a)
                        case List(a: FVar) => List(a)
                        case List(a: FOpExpr) => isOpExprValidLHS(a) match {
                            case true => a.args match {
                                case List(b: FParam) => List(b)
                                case List(b: FVar) => List(b)
                                case _ => throw new Exception("Invalid LHS in assignment: " + lhs)
                            }
                            case false => throw new Exception("Invalid LHS in assignment: " + lhs)
                        }
                        case _ => throw new Exception("Invalid LHS in assignment: " + lhs)
                    }
                    case false => throw new Exception("Invalid LHS in assignment: " + lhs)
                } 
                case _ => throw new Exception("Unexpected LHS in assignment: " + lhs)
            }
            case FBlock(stmts) => stmts.flatMap(_modifiesState)
            case FIfStmt(cond, thenStmt) => _modifiesState(thenStmt)
            case FIfElseStmt(cond, thenStmt, elseStmt) => _modifiesState(thenStmt) ++ _modifiesState(elseStmt)
            case FHavoc(v) => List(v)
            case FSkip() => List()
            case FAssume(cond) => SemPatDriver.ERROR("Assume statement in modifiesState")
        }).distinct
        mod_cache(fstmt) = mods
        mods
    }

    def usesState (fexpr : FExpr) : List[FStateVar] = {
        if (use_expr_cache.contains(fexpr)) return use_expr_cache(fexpr)
        val uses = (fexpr match {
            case a: FParam => List(a)
            case a: FVar => List(a)
            case e: FOpExpr => e.args.flatMap(usesState) ++ (e.op match {
                case FBVExtract(he, le) => usesState(he) ++ usesState(le)
                case FArrayIndex(e) => usesState(e)
                case _ => List()
            })
            case FFuncInvocation(id, args) => args.flatMap(usesState)
            case FITEExpr(cond, thn, els) => usesState(cond) ++ usesState(thn) ++ usesState(els)
            case _ => List()
        }).distinct
        use_expr_cache(fexpr) = uses
        uses
    }

    def usesState (fstmt: FStmt) : List[FStateVar] = {
        if (use_cache.contains(fstmt)) return use_cache(fstmt)
        val uses = (fstmt match {
            case FAssignStmt(lhs, rhs) => usesState(rhs) ++ (lhs match {
                case e: FOpExpr => isOpExprValidLHS(e) match {
                    case true => e.op match {
                        case FArrayIndex(_) | FBVExtract(_, _) => e.args match {
                            case List(a: FParam) => List(a)
                            case List(a: FVar) => List(a)
                            case _ => throw new Exception("Invalid LHS in assignment: " + lhs)
                        }
                        case _ => List()
                    }
                    case false => throw new Exception("Invalid LHS in assignment: " + lhs)
                } 
                case _ => List()
            })
            case FBlock(stmts) => stmts.flatMap(usesState)
            case FIfStmt(cond, thenStmt) => usesState(thenStmt) ++ usesState(cond)
            case FIfElseStmt(cond, thenStmt, elseStmt) => usesState(thenStmt) ++ usesState(elseStmt) ++ usesState(cond)
            case FHavoc(v) => List()
            case FSkip() => List()
            case FAssume(cond) => SemPatDriver.ERROR("Assume statement in usesState")
        }).distinct
        use_cache(fstmt) = uses
        uses
    }

    def usesSummary (fexpr : FExpr) : ModSummary = {
        fexpr match {
            case a: FParam => Map(FBoolLit(true) -> List(a))
            case a: FVar => Map(FBoolLit(true) -> List(a))
            case e: FOpExpr => Map(FBoolLit(true) -> (e.args.flatMap(usesState) ++ (e.op match {
                case FBVExtract(he, le) => usesState(he) ++ usesState(le)
                case FArrayIndex(e) => usesState(e)
                case _ => List()
            })))
            case FFuncInvocation(id, args) => Map(FBoolLit(true) -> args.flatMap(usesState))
            case FITEExpr(cond, thn, els) => Map(cond -> usesState(thn), (!cond) -> usesState(els))
            case _ => Map(FBoolLit(true) -> List())
        }
    } 

    def traceBack (fstmt: FStmt, fv: FStateVar) : List[FStateVar] = {
        clearCache()
        _traceBack(fstmt, fv)
    }

    def _traceBack (fstmt: FStmt, fv: FStateVar) : List[FStateVar] = {
        if (trace_cache.contains((fstmt, fv))) return trace_cache((fstmt, fv))
        val taints = (fstmt match {
            case FAssignStmt(lhs, rhs) => (lhs match {
                case a: FStateVar => if (a == fv) usesState(rhs) else List()
                case e: FOpExpr => e.op match {
                    case FArrayIndex(_) | FBVExtract(_, _) => e.args match {
                        case List(a: FStateVar) => if (a == fv) usesState(rhs) else List()
                        case List(a: FOpExpr) => a.op match {
                            case FArrayIndex(_) | FBVExtract(_, _) => a.args match {
                                case List(b: FStateVar) => if (b == fv) usesState(rhs) else List()
                                case _ => throw new Exception("Invalid LHS in assignment: " + lhs)
                            }
                            case _ => throw new Exception("Invalid LHS in assignment: " + lhs)
                        }
                        case _ => throw new Exception("Invalid LHS in assignment: " + lhs)
                    }
                    case _ => throw new Exception("Invalid LHS in assignment: " + lhs)
                } 
                case _ => List()
            })
            case FBlock(stmts) => stmts.foldRight[List[FStateVar]](List(fv))((s, acc) => 
                (acc.flatMap(a => {val _res = _traceBack(s, a); if (_res.length == 0) List(a) else _res})).distinct)
            case FIfStmt(cond, thenStmt) => _traceBack(thenStmt, fv) ++ 
                (if (_modifiesState(thenStmt).contains(fv)) usesState(cond) else List())
            case FIfElseStmt(cond, thenStmt, elseStmt) => _traceBack(thenStmt, fv) ++ _traceBack(elseStmt, fv) ++ 
                (if (_modifiesState(thenStmt).contains(fv) || _modifiesState(elseStmt).contains(fv)) usesState(cond) else List())
            case FHavoc(v) => List()
            case FSkip() => List()
            case FAssume(cond) => SemPatDriver.ERROR("Assume statement in traceBack")
        }).distinct
        trace_cache((fstmt, fv)) = taints
        taints
    }
}

