import HodgeLean.Foundations.RationalHomologyManifold.RelativeSubdivisionIteration
import HodgeLean.Foundations.RationalHomologyManifold.RelativeBoundaryNeighborhood

/-! Detection of original relative classes from actual subdivided boundary representatives.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- An actual subdivided relative boundary forces the original projected cycle class to vanish.
Source: Hatcher, Algebraic Topology, section 2.1; subdivision invariance and relative cycle representatives.
HC no distance; AV milestone no distance.
-/
theorem relativeCycleClass_zero_of_subdivided_boundary (P : TopPair.{0}) (r n : ℕ)
    (z : (SingularChainComplex ℚ P.fst).X n)
    (hz : (((relativeChainFunctor ℚ).obj P).sc n).g.hom
      (((relativeChainProjection ℚ P).f n).hom z) = 0)
    (b : ((relativeChainFunctor ℚ).obj P).X (n + 1))
    (hb : ((relativeChainFunctor ℚ).obj P).d (n + 1) n b =
      (relativeChainProjection ℚ P).f n ((rationalSubdivisionIterate P.fst r).f n z)) :
    (((relativeChainFunctor ℚ).obj P).sc n).moduleCatHomologyClass
      ⟨((relativeChainProjection ℚ P).f n).hom z, hz⟩ = 0 := by
  let C := (relativeChainFunctor ℚ).obj P
  let π := relativeChainProjection ℚ P
  let ξ : LinearMap.ker (C.sc n).g.hom := ⟨(π.f n).hom z, hz⟩
  let F := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map
    (relativeSubdivisionIterate P r)
  let ξ' := ShortComplex.moduleCatCycleMap F ξ
  have hp := congrArg (fun f => f.f n) (relativeSubdivisionIterate_projection P r)
  have hpz := ConcreteCategory.congr_hom hp z
  change (relativeSubdivisionIterate P r).f n (π.f n z) =
    π.f n ((rationalSubdivisionIterate P.fst r).f n z) at hpz
  have hval : ξ'.val = π.f n ((rationalSubdivisionIterate P.fst r).f n z) := hpz
  have hzero : (C.sc n).moduleCatHomologyClass ξ' = 0 := by
    apply (moduleCycleClass_zero_iff_boundary (C.sc n) ξ').mpr
    let hn := ChainComplex.prev ℕ n
    refine ⟨(C.XIsoOfEq hn).inv.hom b, ?_⟩
    have hd := congrArg (fun f => f.hom b) (C.XIsoOfEq_inv_comp_d hn n)
    exact hd.trans (hb.trans hval.symm)
  have hclass := relativeSubdivisionIterate_cycleClass P r n ξ
  change (C.sc n).moduleCatHomologyClass ξ' = (C.sc n).moduleCatHomologyClass ξ at hclass
  exact hclass.symm.trans hzero

#print axioms relativeCycleClass_zero_of_subdivided_boundary
end HodgeLean.Foundations.RationalHomologyManifold
