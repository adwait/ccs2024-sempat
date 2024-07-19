package secant

package analyzers

import platforms.SyntheticPlatform

import secant.flang._
import secant.flang.FLang._
import secant.tableau._

class SyntheticPlatformTableauGen (
    platform: SyntheticPlatform, 
    genconf: Map[String, Int]) 
    extends PlatformAnalysisConfig with IsTableauGenerator {
    
    import platform._

    val depth = genconf.getOrElse("depth", 3)

    val flow_atoms : Map[TableauFlowEdge, (Int, Int) => FacetPredicate] = (1 until (pdepth-1)).map(mop_ind =>
        TableauFlowEdge(s"data_dep${mop_ind}", mops(mop_ind-1), mops(mop_ind)) -> ((i:Int, j:Int) => FacetPredicateDataDep(
            (Utils.llp(mops(mop_ind-1).rd, i, mops(mop_ind-1)) === Utils.llp(mops(mop_ind).rs1, j, mops(mop_ind)) ||
                Utils.llp(mops(mop_ind-1).rd, i, mops(mop_ind-1)) === Utils.llp(mops(mop_ind).rs2, j, mops(mop_ind)))
        )),
    ).toMap ++ Map(
        TableauFlowEdge(s"data_dep0", LoadOp, mops(0)) -> ((i:Int, j:Int) => FacetPredicateDataDep(
            (Utils.llp(LoadOp.rd, i, LoadOp) === Utils.llp(mops(0).rs1, j, mops(0)) ||
                Utils.llp(LoadOp.rd, i, LoadOp) === Utils.llp(mops(0).rs2, j, mops(0)))
        )),
    )

    val archiflab_atoms : Map[TableauIFLabel, (Int) => FacetPredicateIF] = Map.empty

    val secannotation = PrePostAnnotation (
        pre = rfs.map(rf => (rf, Public())).toMap ++ Map(mem -> Secret()),
        post = Map(attobs -> Public())
    )

    val tgconfig = List(
        TreeTableauSpecificationMultiCon("flow_tabloo", 
            edges = flow_atoms, iflabels = archiflab_atoms, 
            spec = secannotation, depth = depth, wneg = true
        )
    )
}


object SyntheticPlatformTableauGen {
    def apply (plat: MicroPlatform, genconf: Map[String, Int]) : SyntheticPlatformTableauGen = {
        plat match {
            case plat: SyntheticPlatform => new SyntheticPlatformTableauGen(plat, genconf)
            case _ => throw new Exception("SyntheticPlatformTableauGen: platform is not SyntheticPlatform")
        }
    }
}

