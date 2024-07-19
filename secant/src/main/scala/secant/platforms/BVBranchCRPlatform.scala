/**
  * Branch prediction with computation reuse
  * 
  * Uses branch prediction as the speculative mechanism.
  * 
  * Mul instructions are caches in a uop cache (called
  * the reuse_buffer). Instructions with matching operands
  * are reused from the reuse buffer.
  * 
  */
package secant
package platforms

import flang.FLang._
import flang._


case class BVBranchCRPlatformConfig (
    word_width: Int, 
    buffer_id_width: Int,
    has_cache: Boolean, 
    cache_index_width: Int, 
    full_assoc: Boolean
)
object BVBranchCRPlatformConfig {
    def apply (m: Map[String, Int]) : BVBranchCRPlatformConfig = {
        new BVBranchCRPlatformConfig(
            m.getOrElse("word_width", 32), 
            m.getOrElse("buffer_id_width", 3),
            m.getOrElse("has_cache", 0) == 1, 
            m.getOrElse("cache_index_width", 3), 
            m.getOrElse("full_assoc", 0) == 1
        )
    }
}


class BVBranchCRPlatform (conf: BVBranchCRPlatformConfig) extends MicroPlatform with HasSpecFlag with HasState {

    val exe = MicroStage("exe")
    val exeunit = Generator(exe)
    val mstructs: List[MicroStructure] = List(exeunit)

    val ww = conf.word_width
    val cache_index_width = conf.cache_index_width
    val buffer_id_width = conf.buffer_id_width
    assert (ww >= 8, "Word width must be atleast 8")
    
    assert (buffer_id_width > 0, 
        "Buffer must atleast have size 2, to be modelled as a bv indexed array")
    val buffer_size = math.pow(2, conf.buffer_id_width)

    val word_t = bvt(ww)
    val addr_t = bvt(ww-2)
    val regindex_t = bvt(5)
    
    val regfile = FGlobalParam("regfile", arrayt(regindex_t, word_t))
    val mem = FGlobalParam("mem", arrayt(addr_t, word_t))

    // Cache
    val has_cache = conf.has_cache
    val full_assoc = has_cache && conf.full_assoc
    val cache_index_t = bvt(cache_index_width)
    val cache = List(
        FGlobalParam("cache_valid", arrayt(cache_index_t, booleant)),
        FGlobalParam("cache_data", arrayt(cache_index_t, word_t)),
        FGlobalParam("cache_tags", arrayt(cache_index_t, addr_t))
    )
    // valid
    val cache_valid = cache(0)
    // Data values
    val cache_data = cache(1)
    // Tags
    val cache_tags = cache(2)

    // Reuse buffer
    val rub = List(
        FGlobalParam("rub_valid", booleant),
        FGlobalParam("rub_arg1", word_t),
        FGlobalParam("rub_arg2", word_t),
        FGlobalParam("rub_res", word_t)
    )
    // valid
    val rub_valid = rub(0)
    // Data values
    val rub_arg1 = rub(1)
    val rub_arg2 = rub(2)
    // Tags
    val rub_res = rub(3)

    val fpcount = FGlobalParam("fpcount", bvt(3))

    val multiplier = FUFunc("IntMul", List(word_t, word_t), word_t)
    val comparator = FDefine("IntComp", 
        List((FId("a1"), word_t), (FId("a2"), word_t), (FId("a3"), bvt(3))), booleant, args => 
            ite(args(2) === bv(0, 3), !(args(0) === args(1)), 
            ite(args(2) === bv(1, 3), (args(0) === args(1)), !(args(0) < args(1))))
    )

    val stateVars: List[FGlobalParam] = List(mem, regfile, spec, spec_on) ++ 
        rub ++ List(fpcount) ++ (if (has_cache) cache else List())

    val customTypes: List[FType] = List()
    val ufuncs: List[FFunc] = List(multiplier, comparator)

    override val archState: List[FGlobalParam] = stateVars

    object StoreOp extends MicroOp {
        override def toString(): String = "StoreOp"

        val rs1 = FLocalParam("rs1", regindex_t)
        val rs2 = FLocalParam("rs2", regindex_t)
        val addr = FLocalParam("addr", addr_t)
        val data = FLocalParam("data", word_t)
        val imm = FLocalParam("imm", word_t)

        override val parameters: List[FLocalParam] = List(rs1, rs2, addr, data, imm)

        override def functional: Map[MicroStage,FStmt] = Map(
            exe -> block(
                addr := (regfile(rs1) + imm)(UInt(ww-1), UInt(2)),
                data := regfile(rs2),
                mem(addr) := data
            )
        )
    }

    object LoadOp extends MicroOp with HasArchFunctional {
        override def toString(): String = "LoadOp"

        val rs1 = FLocalParam("rs1", regindex_t)
        val imm = FLocalParam("imm", word_t)
        val rd = FLocalParam("rd", regindex_t)
        val addr = FLocalParam("addr", addr_t)
        val data = FLocalParam("data", word_t)
        val spec_local = FLocalParam("spec_local", booleant)

        val l_cacheindex = FLocalParam("l_cacheindex", cache_index_t)

        override val parameters: List[FLocalParam] = 
            List(rs1, imm, rd, addr, data, spec_local) ++ (if (has_cache) List(l_cacheindex) else List())


        def check_all (max_limit: Int) : FStmt = {
            def check_all_helper (i: Int) : FStmt = {
                if (i == max_limit) {
                    block(
                        regfile(rd) := mem((regfile(rs1) + imm)(UInt(ww-1), UInt(2))),
                        cache_valid(l_cacheindex) := trueLit,
                        cache_tags(l_cacheindex) := (regfile(rs1) + imm)(UInt(ww-1), UInt(2)),
                        cache_data(l_cacheindex) := regfile(rd)
                    )
                } else {
                    when (cache_valid(bv(i, cache_index_t.width)) && 
                        (cache_tags(bv(i, cache_index_t.width)) === (regfile(rs1) + imm)(UInt(ww-1), UInt(2)))) (
                        regfile(rd) := cache_data(bv(i, cache_index_t.width))
                    ).otherwise (
                        check_all_helper(i + 1)
                    )
                }
            }
            check_all_helper(0)
        }

        override def functional: Map[MicroStage, FStmt] = Map(
            exe -> block(
                addr := (regfile(rs1) + imm)(UInt(ww-1), UInt(2)),
                // Leave cache imprint
    (if (has_cache) 
        if(full_assoc) check_all(Math.pow(2, cache_index_width).toInt)
        else
                when (cache_valid(addr(UInt(cache_index_width+1), UInt(2))) && 
                    cache_tags(addr(UInt(cache_index_width+1), UInt(2))) === addr) (
                    data := cache_data(addr(UInt(cache_index_width+1), UInt(2)))
                ).otherwise (
                    data := mem(addr),
                    cache_valid(addr(UInt(cache_index_width+1), UInt(2))) := trueLit,
                    cache_data(addr(UInt(cache_index_width+1), UInt(2))) := data,
                    cache_tags(addr(UInt(cache_index_width+1), UInt(2))) := addr
                )
    else        data := mem(addr)),
                // Update the register file
                regfile(rd) := data
            )
        )

        def archfunctional: Map[MicroStage,FStmt] = Map(
            exe -> block(
                addr := (regfile(rs1) + imm)(UInt(ww-1), UInt(2)),
                // Does not modify the cache in architectural mode
                data := mem(addr),
                // Update the register file
                regfile(rd) := data
            )
        )
    }

    object BOp extends BranchOp {
        override def toString(): String = "BOp"

        val rs1 = FLocalParam("rs1", regindex_t)
        val rs2 = FLocalParam("rs2", regindex_t)
        val funct3 = FLocalParam("funct3", bvt(3))
        
        val compresult = FLocalParam("compresult", booleant)
        val spec_local = FLocalParam("spec_local", booleant)

        override def condition: FExpr = compresult || is_spec

        override val parameters: List[FLocalParam] = 
            List(rs1, rs2, spec_local, compresult, funct3)

        override def functional: Map[MicroStage, FStmt] = Map(
            exe -> block(
                when (spec_local) (
                    spec := trueLit
                ),
                compresult := comparator(regfile(rs1), regfile(rs2), funct3)
            )
        )
    }

    object FPALUOp extends MicroOp {

        val rs1 = FLocalParam("rs1", regindex_t)
        val rs2 = FLocalParam("rs2", regindex_t)
        val rd = FLocalParam("rd", regindex_t)

        val op1 = FLocalParam("op1", word_t)
        val op2 = FLocalParam("op2", word_t)
        val data = FLocalParam("data", word_t)
        
        override def toString(): String = "FPALUOp"

        override val parameters: List[FLocalParam] = List(rs1, rs2, op1, op2, rd, data)

        override def functional: Map[MicroStage, FStmt] = Map(
            exe -> block(
                op1 := regfile(rs1),
                op2 := regfile(rs2),
                when ((rub_arg1 === op1) && (rub_arg2 === op2) && rub_valid) (
                    data := rub_res,
                    fpcount := fpcount
                ).otherwise (
                    data := multiplier(op1, op2),
                    rub_arg1 := op1,
                    rub_arg2 := op2,
                    rub_res := data,
                    fpcount := fpcount + bv(1, 3),
                ),
                regfile(rd) := data
            )
        )

    }

    object NOP extends MicroOp {
        override def toString(): String = "NOP"

        override def functional: Map[MicroStage, FStmt] = Map(
            exe -> skip()
        )
    }


    object ALUIOp extends MicroOp {
        override def toString(): String = "ALUIOp"

        val rs1 = FLocalParam("rs1", regindex_t)
        val imm = FLocalParam("imm", word_t)
        val rd = FLocalParam("rd", regindex_t)
        val res = FLocalParam("res", word_t)

        override val parameters: List[FLocalParam] = List(rs1, rd, imm, res)

        override def functional: Map[MicroStage, FStmt] = Map(
            exe -> block(
                // If not modelled properly, this conflicts with partial evaluation
                // res := regfile(rs1) + imm,
                regfile(rd) := res
            )
        )
    }

    object ALUROp extends MicroOp {
        override def toString(): String = "ALUROp"

        val rs1 = FLocalParam("rs1", regindex_t)
        val rs2 = FLocalParam("rs2", regindex_t)
        val rd = FLocalParam("rd", regindex_t)
        val res = FLocalParam("res", word_t)
        
        override val parameters: List[FLocalParam] = List(rs1, rs2, rd, res)

        override def functional: Map[MicroStage, FStmt] = Map(
            exe -> block(
                // Underconstrained (abstract operation)
                regfile(rd) := res
            )
        )
    }

    val connections: List[OpPath] = List(
        LoadOp >>> exe,
        StoreOp >>> exe,
        FPALUOp >>> exe,
        BOp >>> exe,
        ALUIOp >>> exe,
        ALUROp >>> exe,
    )

}

object BVBranchCRPlatform {
    def apply (m: Map[String, Int]) : BVBranchCRPlatform = {
        new BVBranchCRPlatform(BVBranchCRPlatformConfig(m))
    }
}
