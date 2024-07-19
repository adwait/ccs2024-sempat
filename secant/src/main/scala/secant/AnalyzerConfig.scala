/*
 * SemPat Project.
 * 
 * @file AnalyzerConfig.scala
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

 * Analyzer case classes and traits.
 *
 */

package secant

import virparser.VIRAtomicBlock
import virparser.VIRInstruction
import secant.flang.FGlobalParam
import secant.flang.FLocalParam
import secant.tableau.{AbsTableau, TableauGrammar, TableauSpecification}
import virparser.VIRParser
import secant.tableau.TGEps
import virparser.{VIRUnroller, InstPointer, VIRProgram, TaintContext, ProgramTaintAnalysis, PEvalInfo}



trait IsTableauGenerator {
    val tgconfig : List[TableauSpecification] 
}

trait IsOrderingSolver {
    // Ordering solver arguments
    val osolver     : OrderingSolverGeneric
    val mopseq      : List[MicroOp]
}

trait IsProgramAnalyzer {

    // The set of Tableaus to verify against
    def tableaus : List[AbsTableau] = List()

    // The compilation mappings from VIRInstructions to LabeledMicroInstr
    def vircomp (vira: VIRInstruction, peval: Option[PEvalInfo]) : LabeledMicroInstr

    /**
      * Naive matcher that returns all sequential matches of the tableau template in the VIRAtomicBlock.
      *
      * @param virab
      * @param tabl
      * @return
      */
    def getTableauMatches(virab: VIRAtomicBlock, pevals: List[Option[PEvalInfo]], tabl: AbsTableau) : List[List[Int]] = {   
        assert(virab.instructions.length == pevals.length)
        
        val tmopseq = tabl.tableauSeq.map(_._2)
        val pmopseq = (virab.instructions zip pevals).map(a => vircomp(a._1, a._2).mop)

        // Get all slices of pmopseq that are equal to tmopseq
        pmopseq.sliding(tmopseq.length).toList.zipWithIndex.filter(_._1.equals(tmopseq)).map(_._2).map(
            i => (i until (i+tmopseq.length)).toList)
    }
}

abstract class PlatformAnalysisConfig {
    val secannotation : Annotation
}

case class ProgramInputConfig (programfile: String, blocknum: Int, program: List[LabeledMicroProgram], depth: Int) {
    def virab () : List[VIRAtomicBlock] = {
        if (programfile == "") SemPatDriver.ERROR("No program file specified")
        
        val virprogram = VIRParser.parseProgram(scala.io.Source.fromFile(programfile).mkString)
        virprogram.getBlock(blocknum) match {
            case None => SemPatDriver.ERROR(s"Block ${blocknum} not found")
            case Some(virab) => {
                if (depth == 1) List(virab)
                else VIRUnroller.unroll(virprogram, depth, InstPointer(blocknum))
            }
        }
    }

    def getCFG () : String = {
        if (programfile == "") SemPatDriver.ERROR("No program file specified")
        else {
            val virprogram = VIRParser.parseProgram(scala.io.Source.fromFile(programfile).mkString)
            VIRUnroller.getCFGraphDot(VIRUnroller.getEdges(virprogram))
        }
    }

    def getFullProgram () : VIRProgram = {
        if (programfile == "") SemPatDriver.ERROR("No program file specified")
        else VIRParser.parseProgram(scala.io.Source.fromFile(programfile).mkString)
    }

    def validVIR () : Boolean = programfile != "" && blocknum >= 0
    // Uses program as a default
    def getProgram (vircomp : (VIRInstruction, Option[PEvalInfo]) => LabeledMicroInstr, inittc: Option[TaintContext] = None) 
        : List[LabeledMicroProgram] = {
        if (validVIR()) {
            inittc match {
                case None => virab().map(vab => {
                    val tcs = (0 to vab.instructions.length-1).map(_ => None).toList
                    MicroProgram.VIRAtomicBlockToLabeledProgram(vab, vircomp, tcs)
                })
                case Some(tc) => virab().map(vab => {
                    val tcs = ProgramTaintAnalysis.executeBlock(vab, tc).map(_._2).tail
                    MicroProgram.VIRAtomicBlockToLabeledProgram(vab, vircomp, tcs)
                })
            }
        } else program
    }
}
object ProgramInputConfig {
    def apply (mopseq: List[(MicroOp, MicroProgram.ParamAnnotationMap)]) : ProgramInputConfig = ProgramInputConfig(
        programfile = "", blocknum = 0, depth = 1,
        program = List(MicroProgram.seqToLabeledProgram(mopseq:_*))
    )
    def applyEPM (mopseq: List[MicroOp]) : ProgramInputConfig = ProgramInputConfig(
        programfile = "", blocknum = 0, depth = 1,
        program = List(MicroProgram.seqToLabeledProgram(mopseq.map((_, MicroProgram.EPM)):_*))
    )
    def apply (programfile: String, blocknum: Int = -1, depth: Int = 1) : ProgramInputConfig = ProgramInputConfig(
        programfile = programfile, blocknum = blocknum, depth = depth,
        program = List(LabeledMicroSequence(List.empty))
    )
}

/**
  * Default configurations
  */
object DefaultOrderingSolverConfig extends PlatformAnalysisConfig with IsOrderingSolver {
    val secannotation : PrePostAnnotation = PrePostAnnotation(Map.empty, Map.empty)

    val osolver : OrderingSolverGeneric = AlloyInterface
    val mopseq: List[MicroOp] = List()
}
