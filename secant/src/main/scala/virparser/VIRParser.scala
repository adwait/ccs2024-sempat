/*
 * SemPat Project.
 * 
 * @file VIRParser.scala
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

 * Parser for VIR.
 *
 */

package virparser

import scala.util.parsing.input.Positional
import scala.util.parsing.combinator.syntactical._
import scala.util.parsing.combinator.PackratParsers

import scala.language.implicitConversions
import scala.collection.mutable

/** This is a re-implementation of the Scala libraries StdTokenParsers with StdToken replaced by VIRToken. */
trait VIRTokenParsers extends TokenParsers {
  type Tokens <: VIRTokens
  import lexical.{Keyword, IntegerLit, Identifier}

  protected val keywordCache = mutable.HashMap[String, Parser[String]]()

  /** A parser which matches a single keyword token.
   *
   * @param chars    The character string making up the matched keyword.
   * @return a `Parser` that matches the given string
   */
  implicit def keyword(chars: String): Parser[String] =
    keywordCache.getOrElseUpdate(chars, accept(Keyword(chars)) ^^ (_.chars))

  /** A parser which matches an integer literal */
  def integerLit: Parser[IntegerLit] =
    elem("integer", _.isInstanceOf[IntegerLit]) ^^ (_.asInstanceOf[IntegerLit])

  /** A parser which matches an identifier */
  def ident: Parser[String] =
    elem("identifier", _.isInstanceOf[Identifier]) ^^ (_.chars)
}

object VIRParser extends VIRTokenParsers with PackratParsers {
    type Tokens = VIRTokens
    val lexical = new VIRLexical

    // an implicit keyword function that gives a warning when a given word is not in the reserved/delimiters list
    override implicit def keyword(chars : String): Parser[String] = {
      if(lexical.reserved.contains(chars) || lexical.delimiters.contains(chars)) super.keyword(chars)
      else failure("You are trying to parse \""+chars+"\", but it is neither contained in the delimiters list, nor in the reserved keyword list of your lexical object")
    }

    sealed class PositionedString(val str : String) extends Positional
    lazy val KwAtomicBlock = "atomic_block"
    lazy val KwProgram = "program"
    lazy val OpNeg = "-"
    
    lexical.delimiters ++= List("(", ")", ",", "[", "]", "{", "}", ";", ":", OpNeg)
    lexical.reserved += (OpNeg, KwAtomicBlock, KwProgram)

    lazy val Pointer: PackratParser[InstPointer] = 
        { integerLit ^^ {case intLit => InstPointer(intLit.chars.toInt)} }
    lazy val PointerList: PackratParser[List[InstPointer]] = 
        { "[" ~> repsep(Pointer, ",") <~ "]" }

    lazy val Reg: PackratParser[InstIdOp] = 
        { ident ^^ {case i => InstIdOp(i)} }
    
    lazy val Imm: PackratParser[InstImmOp] = { 
        integerLit ^^ { case intLit => InstImmOp(intLit.chars.toInt)} |
        OpNeg ~> integerLit ^^ { case intLit => InstImmOp(-intLit.chars.toInt) }
    }
    
    lazy val Operand: PackratParser[InstOperand] =
        { Reg | Imm }
    lazy val OperandList: PackratParser[List[InstOperand]] =
        { repsep(Operand, ",") }

    lazy val Opcode: PackratParser[InstOpcode] =
        { ident ^^ {case i => InstOpcode(i)} }

    lazy val InstructionHead: PackratParser[InstPointer] =
        { Pointer <~ ":" ^^ { case p => p } }
    lazy val Instruction: PackratParser[VIRInstruction] =
        { InstructionHead ~ Opcode ~ OperandList <~ ";" ^^ { case p ~ o ~ ol => VIRInstruction(p, o, ol) } }
    lazy val InstructionList : PackratParser[List[VIRInstruction]] = {
        rep(Instruction)
    }


    lazy val AtomicBlockHeader : PackratParser[(InstPointer, List[InstPointer])] = {
        KwAtomicBlock ~> ("(" ~> Pointer <~ ",") ~ (PointerList <~ ")") ^^ { case p ~ ps => (p, ps) }
    }
    lazy val AtomicBlock : PackratParser[VIRAtomicBlock] = {
        AtomicBlockHeader ~ ("{" ~> InstructionList <~ "}") ^^ {
            case (start, tgts) ~ il => VIRAtomicBlock(start, tgts, il)
        }
    }
    lazy val AtomicBlocks : PackratParser[List[VIRAtomicBlock]] = 
        { rep(AtomicBlock) }
    
    lazy val ProgramHeader : PackratParser[(String, InstPointer)] = {
        KwProgram ~> ident ~ ("(" ~> Pointer <~ ")") ^^ { case name ~ p => (name, p) }
    }
    lazy val Program : PackratParser[VIRProgram] = {
        ProgramHeader ~ ("{" ~> AtomicBlocks <~ "}") ^^ {
            case (name, start) ~ abs => VIRProgram(name, start, abs)
        }
    }

    def parseProgram(text: String): VIRProgram = {
      val tokens = new PackratReader(new lexical.Scanner(text))
      phrase(Program)(tokens) match {
        case Success(prog, _) => prog
        case NoSuccess(msg, next) => {
          val pos = next.pos
          throw new Exception(s"${pos.line}:${pos.column}: ${msg}")
        }
      }
    }
  }

