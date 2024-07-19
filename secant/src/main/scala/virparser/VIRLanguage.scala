/*
 * SemPat Project.
 * 
 * @file VIRLanguage.scala
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

 * Defines VIR Language
 *
 */

package virparser

import scala.collection.mutable.HashMap
import scalax.collection.Graph
import scalax.collection.edge.LDiEdge
import scalax.collection.io.dot._
import implicits._
import scalax.collection.edge.LkDiEdge

sealed trait ASTNode

case class InstPointer (loc: Int) extends ASTNode {
    override def toString() = s"${loc}"
}

case class InstOpcode (opcode: String) extends ASTNode {
    override def toString() = s"${opcode}"
}

sealed trait InstOperand extends ASTNode
case class InstIdOp (reg: String) extends InstOperand {
    override def toString() = s"${reg}"
}
case class InstImmOp (imm: Int) extends InstOperand {
    override def toString() = s"${imm}"
}

case class VIRInstruction (loc: InstPointer, opcode: InstOpcode, operands: List[InstOperand]) extends ASTNode {
    override def toString() = s"${loc}: ${opcode} ${operands.mkString(", ")};"
}

case class VIRAtomicBlock (startloc: InstPointer, targets: List[InstPointer], instructions: List[VIRInstruction]) extends ASTNode {
    override def toString() = s"atomic_block(${startloc}, [${targets.mkString(",")}]) {\n${instructions.mkString("\n")}\n}"
}

case class VIRProgram (name: String, entryloc: InstPointer, blocks: List[VIRAtomicBlock]) extends ASTNode {
    override def toString() = s"program ${name}(${entryloc}) {\n${blocks.mkString("\n")}\n}"

    def getBlock(loc: Int): Option[VIRAtomicBlock] = {
        blocks.find(_.startloc.loc == loc)
    }
}

object VIRUnroller {

    sealed abstract class CFType
    case class CFBranch () extends CFType
    case class CFCall () extends CFType
    case class CFReturn () extends CFType
    
    def isFCall (virab: VIRAtomicBlock) : Option[(InstPointer, InstPointer)] = {
        virab.instructions.reverse match {
            case last :: others => {
                val isfcall = last.opcode.opcode == "jal" && 
                    last.operands(0).asInstanceOf[InstIdOp].reg == "ra" &&
                    last.operands(1).isInstanceOf[InstImmOp]
                if (!isfcall) {
                    None
                } else {
                    val othertgt = virab.targets.filterNot(_ == last.loc)
                    othertgt match {
                        case head :: tl => {
                            Some((InstPointer(last.operands(1).asInstanceOf[InstImmOp].imm), head))
                        }
                        case _ => None
                    }
                }
            }
            case _ => None
        }
    }

    /**
      * Create a graph from the connections.
      * This is a directed graph with labelled edges.
      *
      * @return Graph[MicroStructure, LkDiEdge]
      */
    def getCFGraph (edgeList: List[(InstPointer, InstPointer, CFType)]) : Graph[InstPointer, LkDiEdge] = {
        val allEdges = edgeList.map(
            edge => LkDiEdge(edge._1, edge._2)(edge._3)
        )
        val g = Graph.from(Nil, allEdges)
        g
    }
    /**
      * Create a dot file for the corresponding layout graph.
      *
      * @return
      */
    def getCFGraphDot (edgeList: List[(InstPointer, InstPointer, CFType)]) : String = {
        val dotRoot : DotRootGraph = DotRootGraph(
            directed  = true,
            id        = Some("CFGraph"),
            attrStmts = List(DotAttrStmt(Elem.node, List(DotAttr("shape", "record")))),
            attrList  = List(DotAttr("attr_1", "<one>"),
                            DotAttr("attr_2", "<two>")))
        def edgeTransformer(innerEdge: Graph[InstPointer, LkDiEdge]#EdgeT): Option[(DotGraph,DotEdgeStmt)] = 
            innerEdge.edge match {
                case LkDiEdge(source, target, cft) => cft match {
                    case label: CFType => Some(
                        (dotRoot, DotEdgeStmt(source.toString, target.toString,
                            List(DotAttr("label", label.toString)))))
            }}
        getCFGraph(edgeList).toDot(dotRoot, edgeTransformer)
    }

    def getEdges (virp: VIRProgram) : List[(InstPointer, InstPointer, CFType)] = {
        
        var edgeList : List[(InstPointer, InstPointer, CFType)] = List()

        // Performs a DFS over the call graph
        def dfs (currab: VIRAtomicBlock, stack : List[InstPointer], visited : List[InstPointer]) : Unit = {
            
            if (!visited.contains(currab.startloc)) {
                // No explicit targets means that this is function return
                if (currab.targets.length == 0) {
                    // If stack is empty, we're done as nothing to return to
                    if (stack.length != 0) {
                        // Otherwise return to instpointer at top of stack
                        val retloc = stack.head
                        val retblock = virp.getBlock(retloc.loc).get
                        // Add return edge to list
                        edgeList = (currab.startloc, retloc, CFReturn()) :: edgeList
                        // Continue unrolling from the return block
                        dfs(retblock, stack.tail, visited++List(currab.startloc))
                    }
                } else {
                    // Check if this block performs a function call
                    isFCall(currab) match {
                        case Some((jalloc, retloc)) => {
                            // Yes, so add return location to stack and continue unrolling the called function
                            val jalblock = virp.getBlock(jalloc.loc).get
                            // Add edge
                            edgeList = (currab.startloc, jalloc, CFCall()) :: edgeList
                            dfs(jalblock, retloc :: stack, visited++List(currab.startloc))
                        }
                        case None => {
                            // No, so unroll all targets by default
                            currab.targets.foreach(tgt => {
                                // Add edge
                                edgeList = (currab.startloc, tgt, CFBranch()) :: edgeList
                                dfs(virp.getBlock(tgt.loc).get, stack, visited++List(currab.startloc))
                            })
                        }
                    }
                }
            }
        }

        val entryab = virp.getBlock(virp.entryloc.loc).get
        dfs(entryab, List[InstPointer](), List())
        return edgeList
    }


    def unroll (virp: VIRProgram, depth: Int, startloc: InstPointer) : List[VIRAtomicBlock] = {
        
        // The value to shift instpointers by to avoid repetition
        val shiftstep = Math.pow(10, (Math.ceil(Math.log10(virp.blocks.map(_.startloc.loc).max))).toInt).toInt

        // Shift instpoints by shiftval
        def shiftlocs (virab: VIRAtomicBlock, shiftval: Int) : List[VIRInstruction] = {
            virab.instructions.map(inst => inst.copy(loc = InstPointer(inst.loc.loc + shiftval)))
        }

        // Unrolls one more block
        def unrollBlock (currab: VIRAtomicBlock, stack : List[InstPointer], visitCount : Map[InstPointer, Int], restDepth : Int) : List[List[VIRInstruction]] = {
            
            if (restDepth == 0) {
                // We're done as residual depth is zero
                List(List())
            } else {
                // Otherwise atleast add current block
                val newblock = shiftlocs(currab, shiftstep*visitCount(currab.startloc))

                // No explicit targets means that this is function return
                if (currab.targets.length == 0) {
                    if (stack.length == 0) {
                        // If stack is empty, we're done as nothing to return to
                        List(newblock)
                    } else {
                        // Otherwise return to instpointer at top of stack
                        val retloc = stack.head
                        val retblock = virp.getBlock(retloc.loc).get
                        // Continue unrolling from the return block
                        val r1 = unrollBlock(retblock, stack.tail, visitCount + (currab.startloc -> (visitCount(currab.startloc)+1)), restDepth-1)
                        // Append the current block to all possible unrollings
                        r1.map(newblock ++ _)
                    }
                } else {
                    // Check if this block performs a function call
                    isFCall(currab) match {
                        case Some((jalloc, retloc)) => {
                            // Yes, so add return location to stack and continue unrolling the called function
                            val jalblock = virp.getBlock(jalloc.loc).get
                            val r1 = unrollBlock(jalblock, retloc :: stack, visitCount + (currab.startloc -> (visitCount(currab.startloc)+1)), restDepth-1)
                            r1.map(newblock ++ _)
                        }
                        case None => {
                            // No, so unroll all targets by default
                            currab.targets.map(tgt => {
                                val r1 = unrollBlock(virp.getBlock(tgt.loc).get, stack, 
                                    visitCount + (currab.startloc -> (visitCount(currab.startloc)+1)), 
                                    restDepth-1)
                                r1.map(newblock ++ _)
                            }).flatten
                        }
                    }
                }
            }
        }

        val entryab = virp.getBlock(startloc.loc).get
        val r1 = unrollBlock(entryab, List[InstPointer](), Map[InstPointer, Int]().withDefaultValue(0), depth)
        r1.map(insts => VIRAtomicBlock(startloc, List(), insts))
    }
}   