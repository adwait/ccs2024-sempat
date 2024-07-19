/**
  * SyntheticPlatform.scala
  * 
  * Synthetic example of a pipeline of k buffers
  * and a set of operations that propagates data
  * from buffer i to buffer i+1.
  * 
  * Parameterized by the pipeline depth.
  * 
  */

package secant
package platforms

import secant.flang._
import secant.flang.FLang._


case class SyntheticPlatformConfig (
    word_width : Int, 
    pipe_depth : Int)

object SyntheticPlatformConfig {

    def apply (confmap: Map[String, Int]) : SyntheticPlatformConfig = {
        SyntheticPlatformConfig(
            confmap.getOrElse("word_width", 32), 
            confmap.getOrElse("pipe_depth", 2)
        )
    }
}


class SyntheticPlatform (config: SyntheticPlatformConfig) extends MicroPlatform with HasState {


    val exe = MicroStage("execute")
    val exeunit = Generator(exe)
    val mstructs: List[MicroStructure] = List(exeunit)

    val ww = config.word_width
    val pdepth = config.pipe_depth

    val word_t = bvt(ww)
    val addr_t = bvt(ww)
    val r_index_t = bvt(5)
    
    val mem = FGlobalParam("mem", arrayt(addr_t, word_t))

    val rfs : List[FGlobalParam] = (0 to (pdepth-1)).map(
        i => FGlobalParam(s"rf$i", arrayt(r_index_t, word_t))
    ).toList

    val attobs = rfs(pdepth-1)

    val funcop = FUFunc("funcop", List(word_t, word_t), word_t)

    val stateVars = List(mem) ++ rfs

    val customTypes: List[FType] = List(word_t, addr_t, r_index_t)

    val ufuncs: List[FFunc] = List(funcop)

    trait HasRSRD {
        val rs1: FLocalParam
        val rs2: FLocalParam
        val rd: FLocalParam
    }

    class SynPlatMicroOp (val id: Int) extends MicroOp with HasRSRD {

        override def toString(): String = s"SynPlatMicroOp_$id"

        val rs1 = FLocalParam("rs1", r_index_t)
        val rs2 = FLocalParam("rs2", r_index_t)
        val rd = FLocalParam("rd", r_index_t)

        val op1 = FLocalParam("op1", word_t)
        val op2 = FLocalParam("op2", word_t)

        override val parameters: List[FLocalParam] = List(rs1, rs2, rd, op1, op2)

        override def functional: Map[MicroStage,FStmt] = Map(
            exe -> block(
                op1 := rfs(id)(rs1),
                op2 := rfs(id)(rs2),
                (rfs(id+1))(rd) := funcop(op1, op2)
            )
        )
    }

    object SynPlatMicroOp {
        def apply (id: Int) = new SynPlatMicroOp(id)

    }

    object LoadOp extends MicroOp {

        override def toString(): String = s"LoadOp"

        val rs1 = FLocalParam("rs1", r_index_t)
        val imm = FLocalParam("imm", word_t)
        val rd = FLocalParam("rd", r_index_t)
        val addr = FLocalParam("addr", addr_t)
        val data = FLocalParam("data", word_t)

        override val parameters: List[FLocalParam] = List(rs1, imm, rd, addr, data)

        override def functional: Map[MicroStage,FStmt] = Map(
            exe -> block(
                addr := rfs(0)(rs1) + imm,
                data := mem(addr),
                (rfs(0))(rd) := data
            )
        )
    }

    val mops : List[MicroOp with HasRSRD] = (0 until (pdepth-1)).map(SynPlatMicroOp(_)).toList

    val connections = mops.map(
        _ >>> exe
    ) ++ List(
        LoadOp >>> exe
    )
}


object SyntheticPlatform {
    def apply (confmap: Map[String, Int]) : SyntheticPlatform = {
        new SyntheticPlatform(SyntheticPlatformConfig(confmap))
    }
}
