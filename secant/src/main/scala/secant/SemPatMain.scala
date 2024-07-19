/*
 * SemPat Project.
 * 
 * @file SemPatMain.scala
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

import java.time.LocalDateTime
import java.time.format.DateTimeFormatter
import platforms._
import analyzers._
import java.io.FileWriter
import java.io.File

object CmdLineBindings {
    val platforms : Map[String, Map[String, Int] => MicroPlatform] = Map(
        "bvcompre" -> (BVCompReusePlatform(_))
        , "bvssv2" -> (BVSSPlatform(_))
        , "bvstlcr1" -> (BVSTLCRPlatform(_))
        , "bvbranchcr" -> (BVBranchCRPlatform(_))
        , "synthetic" -> (SyntheticPlatform(_))
        , "bvlsqc" -> (BVLSQCachePlatform(_))
    )

    val analyzers : Map[String, (MicroPlatform, Map[String, Int]) => PlatformAnalysisConfig] = Map(
        "bvcompre:an" -> ((p, c) => BVCompReusePlatformAnalyzer(p, c))
        , "bvcompre:tg" -> ((p, c) => BVCompReuseTableauGenerator(p, c))
        , "bvssv2:an" -> ((p, c) => BVSSPlatformAnalyzer(p))
        , "bvssv2:tg" -> ((p, c) => BVSSPlatformTableauGenerator(p, c))
        , "bvstlcr1:tg" -> ((p, c) => BVSTLCRPlatformTableauGenerator(p, c))
        , "bvstlcr1:an" -> ((p, c) => BVSTLCRPlatformAnalyzer(p, c))
        , "bvbranchcr:tg" -> ((p, c) => BVBranchCRPlatformTableauGenerator(p, c))
        , "bvbranchcr:an" -> ((p, c) => BVBranchCRPlatformAnalyzer(p, c))
        , "synthetic:tg" -> ((p, c) => SyntheticPlatformTableauGen(p, c))
        , "bvlsqc:tg" -> ((p, c) => BVLSQCachePlatformTableauGenerator(p, c))
        , "bvlsqc:an" -> ((p, c) => BVLSQCachePlatformAnalyzer(p, c))
    )
}

object SemPatMain {

    lazy val headerFull = s"""
==============================================================
  
  SECANT v0.1: SECurity ANalysis Toolkit, specialized for,
  
  SemPat: Using Hyperproperty-based Semantic Analysis to
        Generate Microarchitectural Attack Patterns
--------------------------------------------------------------

  Author: Adwait Godbole, UC Berkeley (adwait@berkeley.edu)
==============================================================
"""

    val LOGS = "logs"
    val TRACKERFILE = "logs/tracker.log"

    case class FrontendConfig(
        cmd         : Cmd = Help(),
        savelog     : String = "",
        // Platform definition arguments
        platform    : String = null,
        platformcfg : Map[String, Int] = Map(),
        analyzercfg : Map[String, Int] = Map(),
        panalyzer   : String = null,
        proginput   : ProgramInputConfig = ProgramInputConfig(List()),
        limit       : Int = -1,
        verbose     : Int = 1,
        srctcpath   : String = "",
        tgttcpath   : String = ""
    )

    def parseOptions (args: Array[String]) : FrontendConfig = {
        val argParser = new scopt.OptionParser[FrontendConfig]("SemPat") {
            head("SemPat", "0.1")
            help("help").text("prints usage text")
                .children(
                    note(headerFull)
                )
            opt[Int]('v', "verbosity")
                .action((v, c) => c.copy(verbose = v))
                .text("verbosity")
            opt[String]('s', "savelog")
                .action((s, c) => c.copy(savelog = s))
                .text("save run named <name> to log file, not saved if string is empty")
                .valueName("<name>")
            opt[String]('c', "command")
                .required()
                .action((c, cfg) => c match {
                    case "xtab" => cfg.copy(cmd = CheckTableau())
                    case "xhyp" => cfg.copy(cmd = CheckTwoSafety())
                    case "syntab" => cfg.copy(cmd = SynthTableau())
                    case "cfg" => cfg.copy(cmd = CreateCFG())
                    case "taint" => cfg.copy(cmd = AnalyzeTaint())
                    case _ => SemPatDriver.ERROR("Invalid command")
                })
                .text("command to run")
                .valueName("<xtab|xhyp|syntab|cfg|taint>")
            opt[String]('p', "platform")
                .action((b, c) => c.copy(platform = b))
                .text("platform being analyzed")
                .valueName(s"<${CmdLineBindings.platforms.keys.mkString("|")}>")
            opt[Map[String, Int]]('q', "platformcfg")
                .action((p, c) => c.copy(platformcfg = p))
                .text("platform configuration")
                .valueName("<key1>=<value1>,<key2>=<value2>,...")
            opt[String]('a', "analyzer")
                .action((a, c) => c.copy(panalyzer = a))
                .text("platform analyzer plugin")
                .valueName(s"<${CmdLineBindings.analyzers.keys.mkString("|")}>")
            opt[Map[String, Int]]('b', "analyzercfg")
                .action((p, c) => c.copy(analyzercfg = p))
                .text("analyzer configuration")
                .valueName("<key1>=<value1>,<key2>=<value2>,...")
            opt[Int]('l', "limit")
                .action((p, c) => c.copy(limit = p))
                .text("unrolled sequence limit (for taint/x_)")
                .valueName("<limit>")
            opt[String]('f', "filename")
                .action((s, c) => {
                    s.split(":") match {
                        case Array(filename) => c.copy(proginput = ProgramInputConfig(filename))
                        case Array(filename, blockid) => c.copy(proginput = ProgramInputConfig(filename, blockid.toInt))
                        case Array(filename, blockid, depth) => c.copy(proginput = ProgramInputConfig(filename, blockid.toInt, depth.toInt))
                        case _ => SemPatDriver.ERROR("Invalid VIR atomic block format, should be filename:blockid[:depth]")
                    }
                })
                .valueName("<virfile>:<blockid>[:<depth>]")
                .text("program: vir block in format <virfile>:<blockid>[:<depth]")
            opt[String]('t', "srctcpath")
                .action((p, c) => c.copy(srctcpath = p))
                .valueName("<path>")
                .text("path to source taint context file")
            opt[String]('u', "tgttcpath")
                .action((p, c) => c.copy(tgttcpath = p))
                .valueName("<path>")
                .text("path to target taint context file")
            checkConfig(c => 
                if ((c.cmd == CheckTwoSafety() || c.cmd == CheckTableau()) 
                    && (c.proginput.programfile == "" || c.platform == null || c.panalyzer == null)) 
                    failure("Check requires a file to analyze") 
                else if ((c.cmd == AnalyzeTaint()) 
                    && (c.srctcpath == "" || c.tgttcpath == "")) 
                    failure("Taint analysis requires a source and target taint context file")
                else success
            )
        }
        argParser.parse(args, FrontendConfig()).getOrElse(FrontendConfig())
    }

    def main (args: Array[String]) : Unit = {
        val config = parseOptions(args)
        val platform = if (config.platform == null) null else
            CmdLineBindings.platforms(config.platform)(config.platformcfg)
        val panalyzer = if (config.panalyzer == null) null else
            CmdLineBindings.analyzers(config.panalyzer)(platform, config.analyzercfg)
        SemPatDriver.main(
            SemPatDriver.Config(
                cmd = config.cmd,
                platform = platform,
                panalyzer = panalyzer,
                proginput = config.proginput,
                verbose = config.verbose,
                limit = config.limit,
                tcsrcpath = config.srctcpath,
                tctgtpath = config.tgttcpath,
            )
        )

        val logdir = new File(LOGS)
        if (!logdir.exists()) logdir.mkdir()
        val trackerfile = new File(TRACKERFILE)
        if (!trackerfile.exists()) trackerfile.createNewFile()
        val trackerwriter = new FileWriter(trackerfile, true)

        if (config.savelog != "") {
            val datetime = DateTimeFormatter.ofPattern("yyyy:MM:dd:HH:mm:ss").format(LocalDateTime.now())
            // Configuration arguments string
            val configlog = args.mkString(" ")
            // Record the recent run
            val resultlog = new FileWriter(s"logs/${datetime}.log")
            resultlog.write(s"Run name: ${config.savelog}\nTime: ${datetime}\nConfig: ${configlog}\nResult:\n${SemPatDriver.resultString}")
            resultlog.close()
            trackerwriter.write(s"${config.savelog},${datetime}.log\n")
            trackerwriter.close()
            println(s"Saved log for run ${config.savelog} to logs/${datetime}.log")
        }
    }
}