/*
 * SemPat Project.
 * 
 * @file SemPatDriver.scala
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

import secant.platforms._
import secant.tableau._

import scala.util.parsing.combinator._
import java.io._

import com.typesafe.scalalogging.Logger
import secant.flang.FLang
import virparser.VIRAtomicBlock
import virparser.InstPointer
import virparser.ProgramTaintAnalysis
import virparser.TaintContextJSON

sealed abstract class Cmd
case class Help() extends Cmd
case class DotFile() extends Cmd
case class OrderingSolving() extends Cmd
case class SynthTableau() extends Cmd
case class CheckTwoSafety() extends Cmd
case class CheckTableau() extends Cmd
case class AnalyzeTaint() extends Cmd
case class CreateCFG() extends Cmd

object SemPatDriver {

    val logger = Logger("secant.SemPatDriver")
    var mainVerbosity: Int = 1;
    
    case class Config(
        cmd         : Cmd = Help(),
        // Platform definition arguments
        platform    : MicroPlatform = null,
        // Platform analysis arguments
        panalyzer   : PlatformAnalysisConfig = null,
        // Program to be analyzed
        proginput   : ProgramInputConfig = ProgramInputConfig(List()),
        // Unroll limit
        limit       : Int = 10,
        // Taint context inputs
        tcsrcpath   : String = "",
        tctgtpath   : String = "",
        /* 
        verbosities:
        0: essential: print nothing but results and error messages
        1: basic: current default behaviour, includes statuses
        2: stats: includes statistics on time/which properties are being solved
        3: print everything
        */
        verbose     : Int = 1,
    ) 

    var resultString: String = ""


    def main(config: Config) : String = {
        configInfo(s"Verbosity level: ${config.verbose}")
        mainVerbosity = config.verbose
        configInfo(s"Command: ${config.cmd}")

        val pretime = System.nanoTime()

        val result = config.cmd match {
            case DotFile() => {
                val platformdotstring = config.platform.getDotFile()
                val fp = new FileWriter(s"platformfigs/${config.platform}.dot")
                fp.write(platformdotstring)
                fp.close()
                resultInfo(s"Dotfile generated to: platformfigs/${config.platform}.dot")
            }
            case CheckTwoSafety() => {            
                config.platform match {
                    case platform: MicroPlatform with HasState => {
                        config.panalyzer match {
                            case pan: PlatformAnalysisConfig with IsProgramAnalyzer => {
                                // Attempt to grab program from VIRFile
                                val mp = if (config.tcsrcpath == "") {
                                    INFO(s"CheckTwoSafety: No taint context provided")
                                    config.proginput.getProgram(pan.vircomp)
                                } else {
                                    INFO(s"CheckTwoSafety: Using taint context from ${config.tcsrcpath}")
                                    val inittc = TaintContextJSON.parseJSON(
                                        scala.io.Source.fromFile(config.tcsrcpath).getLines().mkString("\n")
                                    )._2
                                    config.proginput.getProgram(pan.vircomp, Some(inittc))
                                }
                                generalInfo(s"Found ${mp.length} sequences\n")
                                var times = List[Double]()
                                var time = System.nanoTime()
                                val result = mp.map(mps => {
                                    time = System.nanoTime()
                                    val res = FunctionalSolver.getTwoSafetyCheck(platform, pan.secannotation, mps)
                                    times = ((System.nanoTime() - time)/1e9)::times
                                    res
                                }).mkString("\n")
                                resultInfo(s"TwoSafety result: \n\n${result}")
                                resultInfo(s"Sequencewise Times: ${times.mkString(",")}")
                            }
                            case pan: PlatformAnalysisConfig => {
                                val mp = config.proginput.program
                                WARN("CheckTwoSafety: No program analyzer specified. Using raw program input.")

                                generalInfo(s"Found ${mp.length} sequences\n")
                                var times = List[Double]()
                                var time = System.nanoTime()
                                val result = mp.map(mps => {
                                    time = System.nanoTime()
                                    val res = FunctionalSolver.getTwoSafetyCheck(platform, pan.secannotation, mps)
                                    times = ((System.nanoTime() - time)/1e9)::times
                                    res
                                }).mkString("\n")
                                resultInfo(s"TwoSafety result: \n\n${result}")
                                resultInfo(s"Sequencewise Times: ${times.mkString(",")}")
                            }
                            case _ => ERROR("CheckTwoSafety: The platform analyzer does not have a program analyzer.")
                        }
                    }
                    case _ => {
                        ERROR("TwoSafety: The platform does not have state variables.")
                    }
                }
            }
            case OrderingSolving() => {
                config.panalyzer match {
                    case pan: PlatformAnalysisConfig with IsOrderingSolver => {
                        val orderings = pan.osolver.solvePlatform(config.platform, pan.mopseq)
                        resultInfo(s"Orderings: \n\n${orderings}")
                    }
                    case _ => {
                        ERROR("OrderingSolving: The platform analyzer does not have an ordering solver.")
                    }
                }
            }
            case SynthTableau() => {
                config.platform match {
                    case platform: MicroPlatform with HasState => {
                        config.panalyzer match {
                            case pan : PlatformAnalysisConfig with IsTableauGenerator => {
                                val result = TableauGenerationEngine.generateTableau(platform, pan.tgconfig).map(
                                    t => s"${t._1.toString()}:\n${t._2.mkString("\n")}"
                                )
                                resultInfo(s"Tableaus found: \n\n${result.mkString("\n")}")
                            }
                            case _ => ERROR("SynthTableau: The platform analyzer does not have a tableau generator.")
                        }
                    }
                    case _ => ERROR("SynthTableau: The platform does not have state variables.")
                }
            }
            case CheckTableau() => {
                config.platform match {
                    case platform: MicroPlatform with HasState => {
                        config.panalyzer match {
                            case pan: PlatformAnalysisConfig with IsProgramAnalyzer => {
                                val virablist = config.proginput.virab
                                generalInfo(s"Found ${virablist.length} sequences\n")
                                var times = List[Double]()
                                var time = System.nanoTime()

                                val result = if (config.tcsrcpath == "") {
                                    INFO(s"CheckTableau: No taint context provided")

                                    virablist.map(virab => {
                                        time = System.nanoTime()
                                        val res = pan.tableaus
                                            .map(tabl => FunctionalSolver.getTableauCheck(platform, pan, virab, tabl, 
                                                (0 to virab.instructions.length-1).map(_ => None).toList))
                                            .mkString("\n")
                                        times = ((System.nanoTime() - time)/1e9)::times
                                        res
                                    }).mkString("\n")
                                } else {
                                    INFO(s"CheckTableau: Using taint context from ${config.tcsrcpath}")
                                    val inittc = TaintContextJSON.parseJSON(
                                        scala.io.Source.fromFile(config.tcsrcpath).getLines().mkString("\n")
                                    )._2

                                    virablist.map(virab => {
                                        time = System.nanoTime()
                                        val res = pan.tableaus
                                            .map(tabl => FunctionalSolver.getTableauCheck(platform, pan, virab, tabl, 
                                                ProgramTaintAnalysis.executeBlock(virab, inittc).tail.map(_._2)))
                                            .mkString("\n")
                                        times = ((System.nanoTime() - time)/1e9)::times
                                        res
                                    }).mkString("\n")
                                }
                                resultInfo(s"Tableau check result: \n\n${result}")
                                resultInfo(s"Sequencewise Times: ${times.mkString(",")}")
                            }
                            case _ => ERROR("CheckTableau: The platform analyzer does not have a program analyzer.")
                        }
                    }
                    case _ => {
                        ERROR("CheckTableau: The platform does not have state variables.")
                    }
                }
            }
            case CreateCFG() => {
                val programdotstring = config.proginput.getCFG()
                val basename = (new File(config.proginput.programfile)).getName()
                val fp = new FileWriter(s"programfigs/${basename}.dot")
                fp.write(programdotstring)
                fp.close()
                resultInfo(s"Dotfile generated to: programfigs/${config.proginput.programfile}.dot")
            }
            case AnalyzeTaint() => {
                // Write out contexts to files        
                val itcstring = scala.io.Source.fromFile(config.tcsrcpath)
                    .getLines().mkString("\n")
                
                val contexts = ProgramTaintAnalysis.performAnalysis(
                    config.proginput.getFullProgram(), itcstring, config.limit)
        
                contexts.foreach{case (loc, context) => {
                    val fileWriter = new FileWriter(
                        new File(s"${config.tctgtpath}/taintcontext_${loc}.json"))
                    fileWriter.write(context)
                    fileWriter.close()
                }}
            }
            case Help() => ""
        }
        val posttime = System.nanoTime()
        resultInfo(s"Total time: ${(posttime - pretime)/1e9} seconds")
        INFO(resultString)
        println(resultString)
        resultString
    }

    def DEBUG (s: Any) = {
        if (mainVerbosity >= 3)
            logger.debug(s"DEBUG: ${s}")
    }
    def INFO (s: Any) = {
        if (mainVerbosity >= 2)
            logger.info(s"INFO: ${s}")
    }
    def WARN (s: String) = {
        if (mainVerbosity >= 1)
            logger.warn(s"WARNING: ${s}")
    }
    def ERROR (s: String) = {
        logger.error(s"ERROR: ${s}")
        throw new Exception(s)
    }

    def configInfo (s : String) = {
        INFO(s"  > ${s}")
    }
    def generalInfo (s: String) : String = {
        resultString += s" ${s}\n"
        resultString
    }
    def resultInfo (s : String) : String = {
        resultString += "---- result -----------------\n"
        resultString += s" ${s}\n"
        resultString += "---- end result -------------\n"
        resultString
    }
}
