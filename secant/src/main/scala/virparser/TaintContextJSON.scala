/*
 * SemPat Project.
 * 
 * @file TaintContextJSON.scala
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
 * Dumps Taint-analysis results into a JSON File.
 *
 */

package virparser

import io.circe.parser._
import io.circe.ACursor
import io.circe.Json

import scala.collection.immutable.ListMap

object TaintContextJSON {

    def parseTaintContext (pc : Int, taintcontext: ACursor) : TaintContext = {
        
        val regs = taintcontext.downField("regs")
        val regvals : scala.collection.mutable.Map[String, AbsValue] = regs.keys match {
            case None => scala.collection.mutable.Map.empty
            case Some(value) => scala.collection.mutable.Map() ++ value.map(k => {
                val _c = regs.downField(k)
                val value = _c.get[Int]("value") match {
                    case Left(value) => throw new Error("TaintContextReader: value not found")
                    case Right(value) => value
                }
                val taint = _c.get[Boolean]("taint") match {
                    case Left(value) => throw new Error("TaintContextReader: taint not found")
                    case Right(value) => value
                }
                val at : AbsValue = (_c.get[String]("abstype") match {
                    case Left(value) => throw new Error("TaintContextReader: abstype not found")
                    case Right(value) => value
                }) match {
                    case "c" => ConcVal(value, taint)
                    case "a" => Address(value, taint)
                    case "t" => Top(taint)
                    case _: String => throw new Error("TaintContextReader: abstype not recognized")
                }
                (k, at)
            }).toMap
        }

        val stack = taintcontext.downField("stack")
        val stackvals : scala.collection.mutable.Map[Address, AbsValue] = stack.keys match {
            case None => scala.collection.mutable.Map.empty
            case Some(value) => collection.mutable.Map() ++ value.map(k => {
                val _c = stack.downField(k)
                val taint = _c.get[Boolean]("taint") match {
                    case Left(value) => throw new Error("TaintContextReader: taint not found")
                    case Right(value) => value
                }
                val at : AbsValue = (_c.get[String]("abstype") match {
                    case Left(value) => throw new Error("TaintContextReader: abstype not found")
                    case Right(value) => value
                }) match {
                    case "c" => ConcVal(_c.get[Int]("value") match {
                            case Left(value) => throw new Error("TaintContextReader: value not found")
                            case Right(value) => value
                        }, taint)
                    case "a" => Address(_c.get[Int]("value") match {
                            case Left(value) => throw new Error("TaintContextReader: value not found")
                            case Right(value) => value
                        }, taint)
                    case "t" => Top(taint)
                    case _: String => throw new Error("TaintContextReader: abstype not recognized")
                }
                (Address(k.toInt), at)
            }).toMap
        }
        val tc = TaintContext(ConcVal(pc, false))
        tc.reg ++= regvals
        tc.stack ++= stackvals
        tc
    }


    def parseHLPairs (pc : Int, hlranges: ACursor) : TaintContext = {

        val ranges : List[(Int, Int, Boolean)] = hlranges.values match {
            case None => List.empty
            case Some(value) => value.map(x => {
                val _c = x.hcursor
                val start = _c.get[Int]("start") match {
                    case Left(value) => throw new Error("TaintContextReader: start not found")
                    case Right(value) => value
                }
                val end = _c.get[Int]("end") match {
                    case Left(value) => throw new Error("TaintContextReader: end not found")
                    case Right(value) => value
                }
                val taint = _c.get[Boolean]("taint") match {
                    case Left(value) => throw new Error("TaintContextReader: taint not found")
                    case Right(value) => value
                }
                (start, end, taint)
            }).toList
        }
        ProgramTaintAnalysis.rangesToContext(pc, ranges)
    }


    def parseJSON (s: String) : (String, TaintContext) = {
        val json = parse(s)

        json match {
            case Left(failure) => throw new Error("Error parsing JSON: " + failure)
            case Right(jsonObj) => {
                val cursor = jsonObj.hcursor

                val functionname = cursor.get[String]("function") match {
                    case Left(value) => throw new Error("TaintContextReader: functionname not found")
                    case Right(value) => value
                }
                val pc = cursor.get[Int]("pc") match {
                    case Left(value) => throw new Error("TaintContextReader: pc not found")
                    case Right(value) => value
                }
                (functionname, (cursor.get[Boolean]("has_full_context") match {
                    case Left(value) => false
                    case Right(value) => value
                }) match {
                    case true => parseTaintContext(pc, cursor.downField("taintcontext"))
                    case false => parseHLPairs(pc, cursor.downField("hlranges"))
                })
            }
        }
    }

    def createJson (functionname: String, tc: TaintContext) : String = {
        val regs = Json.fromFields (ListMap(tc.reg.toSeq.sortBy(_._1):_*).map{
            case (k, v) => (k, v match {
                case Address(a, b) => Json.obj(
                    ("value", Json.fromInt(a.toInt)),
                    ("taint", Json.fromBoolean(b)),
                    ("abstype", Json.fromString("a"))
                )
                case ConcVal(v, b) => Json.obj(
                    ("value", Json.fromInt(v.toInt)),
                    ("taint", Json.fromBoolean(b)),
                    ("abstype", Json.fromString("c"))
                )
                case Top(b) => Json.obj(
                    ("taint", Json.fromBoolean(b)),
                    ("abstype", Json.fromString("t"))
                )
            })
        })
        val stack = Json.fromFields (ListMap(tc.stack.toSeq.sortBy(-_._1.a):_*).map{
            case (k, v) => (k.a.toString, v match {
                case Address(a, b) => Json.obj(
                    ("value", Json.fromInt(a.toInt)),
                    ("taint", Json.fromBoolean(b)),
                    ("abstype", Json.fromString("a"))
                )
                case ConcVal(v, b) => Json.obj(
                    ("value", Json.fromInt(v.toInt)),
                    ("taint", Json.fromBoolean(b)),
                    ("abstype", Json.fromString("c"))
                )
                case Top(b) => Json.obj(
                    ("taint", Json.fromBoolean(b)),
                    ("abstype", Json.fromString("t"))
                )
            })
        })
        val allFields = List(
            ("function", Json.fromString(functionname)),
            ("pc", tc.pc match {
                case ConcVal(value, _) => Json.fromInt(value.toInt)
                case Address(value, _) => Json.fromInt(value.toInt)
                case Top(_) => Json.fromInt(0)
            }),
            ("has_full_context", Json.fromBoolean(true)),
            ("taintcontext", Json.obj(
                ("regs", regs),
                ("stack", stack)
            ))
        )
        Json.fromFields(allFields).toString
    }
}