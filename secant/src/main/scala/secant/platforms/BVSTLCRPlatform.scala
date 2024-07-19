/**
  * Store to load forwarding with over a bitvector word model
  */
package secant
package platforms

import flang.FLang._
import flang._


case class BVSTLCRPlatformConfig (
    word_width: Int, 
    buffer_id_width: Int, 
    has_cache: Boolean, 
    cache_index_width: Int)

object BVSTLCRPlatformConfig {
    def apply (m: Map[String, Int]) : BVSTLCRPlatformConfig = {
        new BVSTLCRPlatformConfig(
            m.getOrElse("word_width", 32), 
            m.getOrElse("buffer_id_width", 3),
            m.getOrElse("has_cache", 0) == 1, 
            m.getOrElse("cache_index_width", 3)
        )
    }
}


class BVSTLCRPlatform (conf: BVSTLCRPlatformConfig) extends MicroPlatform with HasSpecFlag with HasState {

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

    val sb_index_t = bvt(buffer_id_width)
    // Store buffer
    val sbuffer = List(
        FGlobalParam("sbuffer_valid", booleant),
        FGlobalParam("sbuffer_data", word_t),
        FGlobalParam("sbuffer_tags", addr_t)
        // FGlobalParam("sbuffer_valid", arrayt(sb_index_t, booleant)),
        // FGlobalParam("sbuffer_data", arrayt(sb_index_t, word_t)),
        // FGlobalParam("sbuffer_tags", arrayt(sb_index_t, addr_t))
    )
    // valid
    val sbuffer_valid = sbuffer(0)
    // Data values
    val sbuffer_data = sbuffer(1)
    // Tags
    val sbuffer_tags = sbuffer(2)


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


    val store_stalled = FGlobalParam("store_stalled", booleant)

    val fpcount = FGlobalParam("fpcount", bvt(3))

    val multiplier = FUFunc("IntMul", List(word_t, word_t), word_t)

    val stateVars: List[FGlobalParam] = List(mem, regfile, spec, spec_on, store_stalled) ++ 
        sbuffer ++ rub ++ List(fpcount) ++ (if (has_cache) cache else List())

    val customTypes: List[FType] = List()
    val ufuncs: List[FFunc] = List(multiplier)

    override val archState: List[FGlobalParam] = stateVars

    object StoreOp extends MicroOp {
        override def toString(): String = "StoreOp"

        val rs1 = FLocalParam("rs1", regindex_t)
        val rs2 = FLocalParam("rs2", regindex_t)
        val addr = FLocalParam("addr", addr_t)
        val data = FLocalParam("data", word_t)
        val imm = FLocalParam("imm", word_t)

        val slow_local = FLocalParam("slow_local", booleant)

        override val parameters: List[FLocalParam] = List(rs1, rs2, addr, data, imm, slow_local)

        override def functional: Map[MicroStage,FStmt] = Map(
            exe -> block(
                addr := (regfile(rs1) + imm)(UInt(ww-1), UInt(2)),
                data := regfile(rs2),
                when (!store_stalled) (
                    // Stores just modify the value in the memory and push an 
                    //  entry into the store buffer
                    sbuffer_valid := trueLit,
                    sbuffer_data := data,
                    sbuffer_tags := addr,
                    when (!slow_local) (
                        mem(addr) := data
                    ).otherwise ( 
                        store_stalled := trueLit
                    )
                ) otherwise (
                    mem(sbuffer_tags) := sbuffer_data,
                    store_stalled := falseLit,
                    
                    sbuffer_valid := trueLit,
                    sbuffer_data := data,
                    sbuffer_tags := addr,
                    when (!slow_local) (
                        mem(addr) := data
                    ).otherwise ( 
                        store_stalled := trueLit
                    )
                )
            )
        )
    }

    object LoadOp extends MicroOp {
        override def toString(): String = "LoadOp"

        val rs1 = FLocalParam("rs1", regindex_t)
        val imm = FLocalParam("imm", word_t)
        val rd = FLocalParam("rd", regindex_t)
        val addr = FLocalParam("addr", addr_t)
        val data = FLocalParam("data", word_t)
        val spec_local = FLocalParam("spec_local", booleant)

        override val parameters: List[FLocalParam] = 
            List(rs1, imm, rd, addr, data, spec_local)

        override def functional: Map[MicroStage, FStmt] = Map(
            exe -> block(
                // Loads on the speculative path grab the value from the buffer
                when (spec_local) (
                    spec := trueLit
                ),
                addr := (regfile(rs1) + imm)(UInt(ww-1), UInt(2)),
                // If speculating, grab value from memory
                when (is_spec) (
                    data := mem(addr)
                ).otherwise (
                    // Grab value from the memory (non-speculative)
                    when (sbuffer_valid && (sbuffer_tags === addr)) (
                        data := sbuffer_data
                    ).otherwise (
                        data := mem(addr)
                    )
                ),
                // Leave cache imprint
    (if (has_cache) block(
                cache_valid(addr(UInt(cache_index_width+1), UInt(2))) := trueLit,
                cache_data(addr(UInt(cache_index_width+1), UInt(2))) := data,
                cache_tags(addr(UInt(cache_index_width+1), UInt(2))) := addr
    ) else skip()),
                // Update the register file
                regfile(rd) := data
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
                // If not modelled properly, this conflicts with the assumes from the partial evaluation
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
                // res := regfile(rs1) + regfile(rs2),
                regfile(rd) := res
            )
        )
    }

    val connections: List[OpPath] = List(
        LoadOp >>> exe,
        StoreOp >>> exe,
        FPALUOp >>> exe,
        ALUIOp >>> exe,
        ALUROp >>> exe
    )

}

object BVSTLCRPlatform {
    def apply (m: Map[String, Int]) : BVSTLCRPlatform = {
        new BVSTLCRPlatform(BVSTLCRPlatformConfig(m))
    }
}
