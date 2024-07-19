/**
  * Computation reuse platform
  * 
  * Maintains a buffer of computation results for reuse
  * on subsequent operand match
  *
  * Based on the paper (https://dl.acm.org/doi/10.1145/384286.264200).
  * 
  */


package secant
package platforms

import secant.flang._
import secant.flang.FLang._
import secant.flang.FLangAnalyzer._

case class RUBConfig (
    word_width: Int, 
    rubc_size : Int,
    has_cache : Boolean, 
    full_assoc : Boolean, 
    cache_index_width: Int)

object RUBConfig {
    def apply (m: Map[String, Int]) : RUBConfig = {
        new RUBConfig(
            m.getOrElse("word_width", 32), 
            m.getOrElse("rubc_size", 1),
            m.getOrElse("has_cache", 0) == 1, 
            m.getOrElse("full_assoc", 0) == 1, 
            m.getOrElse("cache_index_width", 5)
        )
    }
}

class BVCompReusePlatform (conf: RUBConfig) extends MicroPlatform with HasState {

    val exe = MicroStage("execute")
    val exeunit = Generator(exe)

    val ww = conf.word_width
    val full_assoc = conf.full_assoc
    assert (ww >= 8, "Word width must be at least 8 bits.")

    val word_t = bvt (ww)
    val addr_t = bvt (ww-2)
    val regindex_t = bvt (5)
    
    val rubc_size = conf.rubc_size
    val rubc_ptr_width = Math.max(Math.ceil(Math.log(rubc_size)/Math.log(2)).toInt, 1)
    val rubindex_t = bvt (rubc_ptr_width)
    
    val has_cache = conf.has_cache
    val cache_index_width = conf.cache_index_width
    val cacheindex_t = bvt(cache_index_width)
    val cachetag = FGlobalParam("cachetag", arrayt(cacheindex_t, addr_t))
    val cachemem = FGlobalParam("cachemem", arrayt(cacheindex_t, word_t))
    val cachevalid = FGlobalParam("cachevalid", arrayt(cacheindex_t, booleant))

    val customTypes = List(word_t, addr_t, regindex_t, rubindex_t)

    // System state
    val mem = FGlobalParam("mem", arrayt(addr_t, word_t))
    val regfile = FGlobalParam("regs", arrayt(regindex_t, word_t))

    val reuse_buffer = List(
        FGlobalParam("rub_valid", arrayt(rubindex_t, booleant)),
        FGlobalParam("rub_arg1", arrayt(rubindex_t, word_t)),
        FGlobalParam("rub_arg2", arrayt(rubindex_t, word_t)),
        FGlobalParam("rub_res", arrayt(rubindex_t, word_t))
    )

    val rub_valid = reuse_buffer(0)
    val rub_arg1 = reuse_buffer(1)
    val rub_arg2 = reuse_buffer(2)
    val rub_res = reuse_buffer(3)

    val rubindex = FGlobalParam("rubindex", rubindex_t)
    val fpcount = FGlobalParam("fpcount", integert)

val stateVars = List(regfile, mem, fpcount, rubindex) ++ reuse_buffer ++
        (if (has_cache) List(cachetag, cachemem, cachevalid) else List())
    
    object LoadOp extends MicroOp with HasArchFunctional {
        override def toString(): String = "LoadOp"

        val rs1 = FLocalParam("rs1", regindex_t)
        val imm = FLocalParam("imm", word_t)
        val addr = FLocalParam("addr", addr_t)
        val data = FLocalParam("data", word_t)
        val rd = FLocalParam("rd", regindex_t)
        
        val l_cacheindex = FLocalParam("l_cacheindex", cacheindex_t)

        def check_all (max_limit: Int) : FStmt = {
            def check_all_helper (i: Int) : FStmt = {
                if (i == max_limit) {
                    block(
                        regfile(rd) := mem((regfile(rs1) + imm)(UInt(ww-1), UInt(2))),
                        cachevalid(l_cacheindex) := trueLit,
                        cachetag(l_cacheindex) := (regfile(rs1) + imm)(UInt(ww-1), UInt(2)),
                        cachemem(l_cacheindex) := regfile(rd)
                    )
                } else {
                    when (cachevalid(bv(i, cacheindex_t.width)) && 
                        (cachetag(bv(i, cacheindex_t.width)) === (regfile(rs1) + imm)(UInt(ww-1), UInt(2)))) (
                        regfile(rd) := cachemem(bv(i, cacheindex_t.width))
                    ).otherwise (
                        check_all_helper(i + 1)
                    )
                }
            }
            check_all_helper(0)
        }

        def check_at (addr: FExpr, index_width: Int) : FStmt = {
            val index_ = addr(UInt(index_width+1), UInt(2))
            when (cachevalid(index_) && (cachetag(index_) === (regfile(rs1) + imm)(UInt(ww-1), UInt(2)))) (
                regfile(rd) := cachemem(index_)
            ).otherwise (
                regfile(rd) := mem((regfile(rs1) + imm)(UInt(ww-1), UInt(2))),
                cachevalid(index_) := trueLit,
                cachetag(index_) := (regfile(rs1) + imm)(UInt(ww-1), UInt(2)),
                cachemem(index_) := regfile(rd)
            )
        }

        override val parameters = List(rs1, imm, addr, data, rd) ++ (if (has_cache) List(l_cacheindex) else List())
        
        override def functional : Map[MicroStage, FStmt] = Map(
            exe -> block(
                addr := (regfile(rs1) + imm)(UInt(ww-1), UInt(2)),
                data := mem(addr),
                if (has_cache) {
                    if (full_assoc) check_all(Math.pow(2, cache_index_width).toInt)
                    else check_at((regfile(rs1) + imm)(UInt(ww-1), UInt(2)), cache_index_width)
                } else (
                    regfile(rd) := data
                )
            )
        )

        def archfunctional: Map[MicroStage,FStmt] = Map(
            exe -> block(
                addr := (regfile(rs1) + imm)(UInt(ww-1), UInt(2)),
                data := mem(addr),
                regfile(rd) := data
            )
        )
    }

    object StoreOp extends MicroOp {
        override def toString(): String = "StoreOp"

        val rs1 = FLocalParam("rs1", regindex_t)
        val rs2 = FLocalParam("rs2", regindex_t)
        val imm = FLocalParam("imm", word_t)
        val addr = FLocalParam("addr", addr_t)
        val data = FLocalParam("data", word_t)

        override val parameters = List(rs1, rs2, imm, addr, data)
        
        override def functional : Map[MicroStage, FStmt] = Map(
            exe -> block(
                addr := (regfile(rs1) + imm)(UInt(ww-1), UInt(2)),
                data := regfile(rs2),
                mem(addr) := data
            )
        )
    }

    def return_rob_search(cond: (FExpr => FExpr), tbody: (FExpr => FStmt), ebody: (FExpr => FStmt)) : FStmt = {
        def return_rob_search_helper(iter: Int, width: Int, cond: (FExpr => FExpr), tbody: (FExpr => FStmt), ebody : (FExpr => FStmt)) : FStmt = {
            iter match {
                case -1 => ebody(bv(0, width))
                case _ => {
                    when (cond(bv(iter, width))) (
                        tbody(bv(iter, width))
                    ).otherwise (
                        return_rob_search_helper(iter-1, width, cond, tbody, ebody)
                    )
                }
            }
        }
        return_rob_search_helper (rubc_size-1, rubc_ptr_width, cond, tbody, ebody)
    }

    object FPALUOp extends MicroOp with HasArchFunctional {
        override def toString(): String = "FPALUOp"

        val rs1 = FLocalParam("rs1", regindex_t)
        val rs2 = FLocalParam("rs2", regindex_t)
        val rd = FLocalParam("rd", regindex_t)
        val op1 = FLocalParam("op1", word_t)
        val op2 = FLocalParam("op2", word_t)
        val res = FLocalParam("res", word_t)
        val local_rubind = FLocalParam("local_rubind", rubindex_t)

        override val parameters = List(rs1, rs2, rd, op1, op2, res, local_rubind)
        
        override def functional : Map[MicroStage, FStmt] = Map (
            exe -> block(
                op1 := regfile(rs1),
                op2 := regfile(rs2),
                return_rob_search(
                    (i: FExpr) => (rub_arg1(i) === op1 && rub_arg2(i) === op2 && rub_valid(i)),
                    (i: FExpr) => block(
                        fpcount := fpcount,
                        regfile(rd) := rub_res(i)
                    ),
                    (i: FExpr) => block(
                        fpcount := fpcount+UInt(1),
                        res := FFuncInvocation(multiplier, List(op1, op2)),
                        regfile(rd) := res,
                        rub_arg1(i) := op1,
                        rub_arg2(i) := op2,
                        rub_res(i) := res,
                        rub_valid(i) := trueLit
                    )
                ),
                res := FFuncInvocation(multiplier, List(op1, op2)),
                regfile(rd) := res    
            )
        )
        
        override def archfunctional : Map[MicroStage, FStmt] = Map (
            exe -> block(
                op1 := regfile(rs1),
                op2 := regfile(rs2),
                res := FFuncInvocation(multiplier, List(op1, op2)),
                regfile(rd) := res
            )
        )
    }

    object IntALUOp extends MicroOp {
        override def toString(): String = "IntALUOp"

        val rs1 = FLocalParam("rs1", regindex_t)
        val rs2 = FLocalParam("rs2", regindex_t)
        val rd = FLocalParam("rd", regindex_t)
        val op1 = FLocalParam("op1", word_t)
        val op2 = FLocalParam("op2", word_t)

        override val parameters = List(rs1, rs2, rd, op1, op2)
        
        override def functional : Map[MicroStage, FStmt] = Map (
            exe -> block(
                op1 := regfile(rs1),
                op2 := regfile(rs2),
                regfile(rd) := FFuncInvocation(alufunction, List(op1, op2))
            )
        )
    }

    object NOP extends MicroOp {
        override def toString(): String = "NOP"

        override def functional : Map[MicroStage, FStmt] = Map (
            exe -> block(
                skip()
            )
        )
    }

    def flush_rob () : Seq[FStmt] = {        
        (0 to rubc_size-1).map(i =>
            rub_valid(bv(i, rubc_ptr_width)) := falseLit
        )
    }
    
    object RFlush extends MicroOp {
        override def toString(): String = "RFlush"
        override def functional: Map[MicroStage, FStmt] = Map(
            exe -> block(flush_rob(): _*)
        )
    }

    // Functions
    val multiplier = FUFunc("IntMul", List(word_t, word_t), word_t)
    val alufunction = FUFunc("IntALU", List(word_t, word_t), word_t)

    val ufuncs = List(multiplier, alufunction)

    override val archState: List[FGlobalParam] = List(regfile, mem)

    val connections = List(
        LoadOp >>> exe,
        StoreOp >>> exe,
        IntALUOp >>> exe,
        FPALUOp >>> exe,
        RFlush >>> exe,
        NOP >>> exe
    )

    val mstructs = List(exeunit)
}

object BVCompReusePlatform {
    def apply (conf: Map[String, Int]) : BVCompReusePlatform = {
        new BVCompReusePlatform(RUBConfig(conf))
    }
}
