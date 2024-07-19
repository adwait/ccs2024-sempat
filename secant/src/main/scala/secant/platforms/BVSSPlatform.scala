/**
  * BVSSPlatform.scala
  * 
  * BVSS platform models the silent stores and load speculation
  * optimizations. It maintains a Load Store Queue Cache (LSQC)
  * that tracks previous loads and stores. 
  * 
  * A store on the same address with the same value is squashed 
  * if present in the LSQC cache.
  * As a side-optimization, a subsequent load on the same address 
  * replays the data from the LSQC cache. 
  * Based on the paper (https://dl.acm.org/doi/pdf/10.1145/360128.360133)
  * 
  */

package secant
package platforms

import secant.flang.FLang._
import secant.flang._


case class BVSSConfig (
    word_size : Int, 
    lsqc_setind_width : Int, 
    lsqc_wayind_width: Int, 
    lsqc_ishashed: Boolean, 
    lsqc_isload: Boolean = true)

object BVSSConfig {
    def apply(conf: Map[String, Int]) : BVSSConfig = {
        BVSSConfig(
            // Word width
            conf.getOrElse("word_width", 32), 
            // (Set index) into the cache
            conf.getOrElse("lsqc_setind_width", 0), 
            // (Way index) into a single set
            conf.getOrElse("lsqc_wayind_width", 1), 
            // Is entire index computed via a hash?
            conf.getOrElse("lsqc_ishashed", 0) == 1,
            // Is LSQC updated only on stores or also on loads.
            conf.getOrElse("lsqc_isload", 0) == 1)
    }
}



class BVSSPlatform (conf: BVSSConfig) extends MicroPlatform with HasState {

    val exe = MicroStage("execute")
    val exeunit = Generator(exe)

    val word_size = conf.word_size
    val lsqc_size = Math.pow(2, conf.lsqc_setind_width+conf.lsqc_wayind_width).toInt
    val lsqc_setind_width = conf.lsqc_setind_width
    val lsqc_wayind_width = conf.lsqc_wayind_width

    assert(word_size > 2, "Word size must be greater than 2")
    val word_t = bvt (word_size)
    val addr_t = bvt (word_size-2)
    val regindex_t = bvt (5)
    val lsqc_t = bvt (lsqc_setind_width+lsqc_wayind_width)

    val customTypes = List(word_t, addr_t, regindex_t, lsqc_t)

    // System state
    val mem = FGlobalParam("mem", arrayt(addr_t, word_t))
    val regfile = FGlobalParam("regs", arrayt(regindex_t, word_t))

    // LSQ Cache
    val lsqc_addr = FGlobalParam("lsqc_addr", arrayt(lsqc_t, addr_t))
    val lsqc_data = FGlobalParam("lsqc_data", arrayt(lsqc_t, word_t))
    // val lsqc_isload = FGlobalParam("lsqc_isload", arrayt(lsqc_t, booleant))
    val lsqc_valid = FGlobalParam("lsqc_valid", arrayt(lsqc_t, booleant))

    // Only uses to index into a way (if non-associative, it is not used)
    val lsptr_t = if (lsqc_wayind_width > 0) bvt(lsqc_wayind_width) else booleant
    val lsptr = FGlobalParam("lsptr", lsptr_t)

    val lscount = FGlobalParam("lscount", integert)

    object LoadOp extends MicroOp {
        override def toString(): String = "LoadOp"

        val rs1 = FLocalParam("rs1", regindex_t)
        val imm = FLocalParam("imm", word_t)
        val addr = FLocalParam("addr", addr_t)
        val data = FLocalParam("data", word_t)
        val rd = FLocalParam("rd", regindex_t)
        val addrhash_expr = concat_index_set_bv(addr, lsqc_hash(addr))

        override val parameters = List(rs1, imm, addr, data, rd)
        override def functional : Map[MicroStage, FStmt] = Map(
            exe -> (
                if (conf.lsqc_isload) block(
                    addr := (regfile(rs1) + imm)(UInt(word_size-1), UInt(2)),

                    data := mem(addr),
                    return_lsqc_search_hash (
                        lsqc_valid(addrhash_expr),
                        //  && lsqc_addr(addrhash_expr) === addr,
                        block (
                            lsqc_addr(addrhash_expr) := addr,
                            lsqc_valid(addrhash_expr) := trueLit,
                            lsqc_data(addrhash_expr) := data
                        ),
                        skip()
                    ),

                    regfile(rd) := data
                ) else block(
                    addr := (regfile(rs1) + imm)(UInt(word_size-1), UInt(2)),
                    data := mem(addr),
                    regfile(rd) := data
                )
            )
        )
    }

    def concat_index_set_bv (a1: FExpr, a2: FExpr) : FExpr = {
        // Fully associative (hashed or otherwise)
        if (lsqc_setind_width == 0) a2
        // Non-associative (associativity = 1)
        else if (lsqc_wayind_width == 0) a1(UInt(lsqc_setind_width-1), UInt(0))
        // Combined set and way index
        else a1(UInt(lsqc_setind_width-1), UInt(0)) ++ a2
    }

    def return_lsqc_search_all (addr_ : FExpr, cond: (FExpr => FExpr), 
        tbody: (FExpr => FStmt), ebody: (FExpr => FStmt)) : FStmt = {        

        def return_lsqc_search_helper(iter: Int, cond: (FExpr => FExpr), tbody: (FExpr => FStmt), ebody : (FExpr => FStmt)) : FStmt = {
            iter match {
                case -1 => ebody(concat_index_set_bv(addr_, lsptr))
                case _ => {
                    when (cond(concat_index_set_bv(addr_, bv(iter, lsqc_wayind_width)))) (
                        tbody(concat_index_set_bv(addr_, bv(iter, lsqc_wayind_width)))
                    ).otherwise (
                        return_lsqc_search_helper(iter-1, cond, tbody, ebody)
                    )
                }
            }
        }

        return_lsqc_search_helper(Math.pow(2, lsqc_wayind_width).toInt-1, cond, tbody, ebody)
    }

    def return_lsqc_search_hash (cond: FExpr, tbody: FStmt, ebody: FStmt) : FStmt = {
        when(cond)(tbody).otherwise(ebody)
    }

    val lsqc_hash = FUFunc("lsqc_hash", List(addr_t), lsptr_t)

    object StoreOp extends MicroOp {
        override def toString(): String = "StoreOp"

        val rs1 = FLocalParam("rs1", regindex_t)
        val rs2 = FLocalParam("rs2", regindex_t)
        val imm = FLocalParam("imm", word_t)
        val addr = FLocalParam("addr", addr_t)
        val data = FLocalParam("data", word_t)

        val addr_hash = FLocalParam("hash", lsptr_t)

        override val parameters = List(rs1, rs2, imm, addr, data, addr_hash)
        
        val addrhash_expr = concat_index_set_bv(addr, lsqc_hash(addr))

        override def functional : Map[MicroStage, FStmt] = Map(
            exe -> block(
                addr := (regfile(rs1) + imm)(UInt(word_size-1), UInt(2)),
                data := regfile(rs2),
                
                addr_hash := lsqc_hash(addr),

if (!conf.lsqc_ishashed) {
        return_lsqc_search_all (
            addr,
            (lsptr_ => (lsqc_valid(lsptr_) && lsqc_addr(lsptr_) === addr)),
            (lsptr_ => when(lsqc_data(lsptr_) === data) (
                skip()
            ).otherwise (
                mem(addr) := data,
                // Set the LSQc entry
                lsqc_addr(lsptr_) := addr,
                lsqc_valid(lsptr_) := trueLit,
                lsqc_data(lsptr_) := data,
                // Increment the LS operation count
                lscount := lscount + UInt(1))),
            (lsptr_ => block(
                mem(addr) := data,
                // Set the LSQc entry
                lsqc_addr(lsptr_) := addr,
                lsqc_valid(lsptr_) := trueLit,
                lsqc_data(lsptr_) := data,
                // Increment the LS operation count
                lscount := lscount + UInt(1)))
        )
} else {
        return_lsqc_search_hash (
            (lsqc_valid(addrhash_expr) && lsqc_addr(addrhash_expr) === addr && 
                lsqc_data(addrhash_expr) === data),
            skip(),
            block (
                mem(addr) := data,
                // Set the LSQc entry
                lsqc_addr(addrhash_expr) := addr,
                lsqc_valid(addrhash_expr) := trueLit,
                lsqc_data(addrhash_expr) := data,
                // Increment the LS operation count
                lscount := lscount + UInt(1)
            )
        )
},
            )
        )
    }

    object ALUIOp extends MicroOp {
        override def toString(): String = "ALUIOp"

        val rs1 = FLocalParam("rs1", regindex_t)
        val imm = FLocalParam("imm", word_t)
        val rd = FLocalParam("rd", regindex_t)
        val op1 = FLocalParam("op1", word_t)
        val op2 = FLocalParam("op2", word_t)

        override val parameters = List(rs1, imm, rd, op1, op2)

        override def functional : Map[MicroStage, FStmt] = Map(
            exe -> block(
                op1 := regfile(rs1),
                regfile(rd) := FFuncInvocation(alufunction, List(op1, imm))
            )
        )
    }

    object ALUROp extends MicroOp {
        override def toString(): String = "ALUROp"

        val rs1 = FLocalParam("rs1", regindex_t)
        val rs2 = FLocalParam("rs2", regindex_t)
        val rd = FLocalParam("rd", regindex_t)
        val op1 = FLocalParam("op1", word_t)
        val op2 = FLocalParam("op2", word_t)

        override val parameters = List(rs1, rs2, rd, op1, op2)

        override def functional : Map[MicroStage, FStmt] = Map(
            exe -> block(
                op1 := regfile(rs1),
                op2 := regfile(rs2),
                regfile(rd) := FFuncInvocation(alufunction, List(op1, op2))
            )
        )
    }

    object NOP extends MicroOp {
        override def toString(): String = "NOP"

        override val parameters = List.empty

        override def functional : Map[MicroStage, FStmt] = Map(
            exe -> skip()
        )
    }

    val alufunction = FUFunc("IntALU", List(word_t, word_t), word_t)

    val stateVars: List[FGlobalParam] = List(mem, regfile, lsqc_addr, lsqc_data, lsqc_valid, lsptr, lscount)

    val ufuncs: List[FFunc] = List(alufunction, lsqc_hash)

    val connections: List[OpPath] = List(
        LoadOp >>> exe,
        StoreOp >>> exe,
        ALUIOp >>> exe,
        ALUROp >>> exe,
    )

    val mstructs = List(exeunit)

}

object BVSSPlatform {
    def apply(conf: Map[String, Int]) : BVSSPlatform = new BVSSPlatform(BVSSConfig(conf))
}
