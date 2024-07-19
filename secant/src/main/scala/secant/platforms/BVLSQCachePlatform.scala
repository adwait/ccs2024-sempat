package secant
package platforms

import flang.FLang._
import flang._

case class BVLSQCacheConfig (
    word_size : Int, 
    lsqc_setind_width : Int,
    lsqc_wayind_width: Int, 
    lsqc_ishashed: Boolean, 
    lsqc_isload: Boolean = true)
object BVLSQCacheConfig {
    def apply(conf: Map[String, Int]) : BVLSQCacheConfig = {
        BVLSQCacheConfig(
            // Word width
            conf.getOrElse("word_width", 32), 
            // (Set index) into the cache
            conf.getOrElse("lsqc_setind_width", 1), 
            // (Way index) into a single set
            conf.getOrElse("lsqc_wayind_width", 1), 
            // Is entire index computed via a hash?
            conf.getOrElse("lsqc_ishashed", 1) == 1,
            // Is LSQC updated only on stores or also on loads.
            conf.getOrElse("lsqc_isload", 0) == 1)
    }
}



class BVLSQCachePlatform (conf: BVLSQCacheConfig) extends MicroPlatform with HasState {

    val exe = MicroStage("execute")
    val exeunit = Generator(exe)

    val word_size = conf.word_size
    val lsqc_size = Math.pow(2, conf.lsqc_setind_width+conf.lsqc_wayind_width).toInt
    val lsqc_setind_width = conf.lsqc_setind_width
    val lsqc_wayind_width = conf.lsqc_wayind_width

    assert(lsqc_wayind_width >= -1, "Way index width must be atleast 1")
    assert(lsqc_setind_width >= -1, "Set index width must be atleast 1")

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

        val addr_hash = FLocalParam("hash", lsptr_t)

        override val parameters = List(rs1, imm, addr, data, rd, addr_hash)
        override def functional : Map[MicroStage, FStmt] = Map(
            exe -> (
                block(
                    addr := (regfile(rs1) + imm)(UInt(word_size-1), UInt(2)),

                    addr_hash := lsqc_hash(addr),

(if (!conf.lsqc_ishashed) return_lsqc_search_all (
                        addr,
                        (ptr_ => lsqc_valid(ptr_) && lsqc_addr(ptr_) === addr),
                        (ptr_ => block (
                            data := lsqc_data(ptr_)
                        )),
                        (block (
                            data := mem(addr),
                            lsqc_addr(concat_index_set_bv(addr, addr_hash)) := addr,
                            lsqc_data(concat_index_set_bv(addr, addr_hash)) := data,
                            lsqc_valid(concat_index_set_bv(addr, addr_hash)) := trueLit,
                            lscount := lscount + UInt(1)
                        ))
                    )
else                return_lsqc_search_hash (
                        lsqc_valid(concat_index_set_bv(addr, addr_hash)) && 
                            lsqc_addr(concat_index_set_bv(addr, addr_hash)) === addr,
                        block (
                            data := lsqc_data(concat_index_set_bv(addr, addr_hash))
                        ),
                        block (
                            data := mem(addr),
                            lsqc_addr(concat_index_set_bv(addr, addr_hash)) := addr,
                            lsqc_data(concat_index_set_bv(addr, addr_hash)) := data,
                            lsqc_valid(concat_index_set_bv(addr, addr_hash)) := trueLit,
                            lscount := lscount + UInt(1)
                        )
                    )
),
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
        tbody: (FExpr => FStmt), ebody: FStmt) : FStmt = {        

        def return_lsqc_search_helper(iter: Int, cond: (FExpr => FExpr), tbody: (FExpr => FStmt), ebody : FStmt) : FStmt = {
            iter match {
                case -1 => ebody
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

    val lsqc_hash = // FUFunc("lsqc_hash", List(addr_t), lsptr_t)
        FDefine("lsqc_hash", List((FId("a"), addr_t)), lsptr_t, 
            if (lsqc_wayind_width == 0) {
                addr => falseLit
            } else {
                addr => addr(0)(UInt(lsqc_wayind_width+lsqc_setind_width-1), UInt(lsqc_setind_width))
            }
        )

    def return_lsqc_flush_all (addr_ : FExpr) : FStmt = {
        block (
            (0 to Math.pow(2, lsqc_wayind_width).toInt-1).map(i =>
                lsqc_valid(concat_index_set_bv(addr_, bv(i, lsqc_wayind_width))) := falseLit
            ): _*
        )
    }

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
            (
                if (!conf.lsqc_ishashed) return_lsqc_flush_all ( addr )
                else    (
                    lsqc_valid(concat_index_set_bv(addr, addr_hash)) := falseLit
                )
            ),
                mem(addr) := data
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
        val res = FLocalParam("res", word_t)


        override val parameters = List(rs1, imm, rd, op1, op2, res)

        override def functional : Map[MicroStage, FStmt] = Map(
            exe -> block(
                op1 := regfile(rs1),
                res := FFuncInvocation(alufunction, List(op1, imm)),
                regfile(rd) := res
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
        val res = FLocalParam("res", word_t)

        override val parameters = List(rs1, rs2, rd, op1, op2, res)

        override def functional : Map[MicroStage, FStmt] = Map(
            exe -> block(
                op1 := regfile(rs1),
                op2 := regfile(rs2),
                res := FFuncInvocation(alufunction, List(op1, op2)),
                regfile(rd) := res
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

    val alufunction = // FUFunc("IntALU", List(word_t, word_t), word_t)
        FDefine("IntALU", List((FId("op1"), word_t), (FId("op2"), word_t)), word_t, 
            a => a(0) + a(1))

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

object BVLSQCachePlatform {
    def apply(conf: Map[String, Int]) : BVLSQCachePlatform = new BVLSQCachePlatform(BVLSQCacheConfig(conf))
}
