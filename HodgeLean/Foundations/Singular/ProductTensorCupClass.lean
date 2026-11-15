import HodgeLean.Foundations.Singular.CupClasses
import HodgeLean.Foundations.Singular.ProductTensorCupCochain
import HodgeLean.Foundations.Singular.ProductCohomologyComparison
import HodgeLean.Foundations.Singular.RationalDualMapNormalization
import HodgeLean.Foundations.Singular.SingularCocyclePullback
import HodgeLean.Foundations.Singular.TensorScalarCycle

/-! The represented projection-cup class under the actual product-chain comparison. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

set_option backward.isDefEq.respectTransparency false in
/-- The actual product-chain comparison sends the scalar tensor cocycle class to the specified projection-cup class.
Source: Hatcher, Algebraic Topology, §3.2, the cohomology cross product and Alexander–Whitney formula. -/
theorem tensorScalarCycle_AW_class (X Y : TopCat.{0}) (p q : ℕ)
    (φ : Cocycle ℚ (TopCat.toSSet.obj X) p) (ψ : Cocycle ℚ (TopCat.toSSet.obj Y) q) :
    AlgebraicTopology.Singular.cochainCohomologyEquiv ℚ (TopCat.of (X × Y)) (p + q)
      ((rationalProductTensorCohomologyEquiv X Y (p + q)).symm
        (((rationalTensorChains X Y).sc (p + q)).linearDual.moduleCatHomologyClass
          (tensorScalarCycle (rationalChains X) (rationalChains Y) p q
            (singularDualCycle X p φ) (singularDualCycle Y q ψ)))) =
    cup (TopCat.of (X × Y)) rfl
      (AlgebraicTopology.Singular.cohomologyMap ℚ p (productFirst X Y) (cohomologyClass X p φ))
      (AlgebraicTopology.Singular.cohomologyMap ℚ q (productSecond X Y) (cohomologyClass Y q ψ)) := by
  let P := TopCat.of (X × Y)
  let n := p + q
  let e := rationalProductTensorHomotopyEquiv X Y
  let t := tensorScalarCycle (rationalChains X) (rationalChains Y) p q
    (singularDualCycle X p φ) (singularDualCycle Y q ψ)
  let f : ((rationalTensorChains X Y).sc n).linearDual ⟶ ((rationalChains P).sc n).linearDual :=
    ShortComplex.linearDualMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map
        (productAlexanderWhitney X Y))
  let ξ := ShortComplex.moduleCatCycleMap f t
  let χ : Cocycle ℚ (TopCat.toSSet.obj P) n := cohomologyCycleToCocycle ℚ n ξ
  let φp := singularCocyclePullback (productFirst X Y) p φ
  let ψp := singularCocyclePullback (productSecond X Y) q ψ
  have hm : (rationalProductTensorCohomologyEquiv X Y n).symm
      (((rationalTensorChains X Y).sc n).linearDual.moduleCatHomologyClass t) =
      ((rationalChains P).sc n).linearDual.moduleCatHomologyClass ξ := by
    change (rationalDualCohomologyHomotopyEquiv e n).symm _ = _
    rw [rationalDualCohomologyHomotopyEquiv_symm]
    change (rationalDualCohomologyHomotopyEquiv e.symm n).toLinearMap _ = _
    rw [rationalDualCohomologyHomotopyEquiv_map]
    exact ShortComplex.moduleCatHomologyClass_naturality f t
  have hc : χ.1 = cupCochain P p q φp.1 ψp.1 := by
    change (tensorScalarCochain (rationalChains X) (rationalChains Y) p q φ.1 ψ.1).comp
      (productAlexanderWhitneyDegree X Y (p + q)) =
        cupCochain P p q (cochainMap ℚ (TopCat.toSSet.map (productFirst X Y)) p φ.1)
          (cochainMap ℚ (TopCat.toSSet.map (productSecond X Y)) q ψ.1)
    exact tensorScalarCochain_AW X Y p q φ.1 ψ.1
  have hclass : AlgebraicTopology.Singular.cochainCohomologyEquiv ℚ P n
      (((rationalChains P).sc n).linearDual.moduleCatHomologyClass ξ) = cohomologyClass P n χ := rfl
  calc
    _ = cohomologyClass P n χ :=
      (congrArg (AlgebraicTopology.Singular.cochainCohomologyEquiv ℚ P n) hm).trans hclass
    _ = cup P rfl (cohomologyClass P p φp) (cohomologyClass P q ψp) :=
      (cup_classes P p q φp ψp χ hc).symm
    _ = _ := congrArg₂
      (fun (a : AlgebraicTopology.Singular.Cohomology ℚ P p)
        (b : AlgebraicTopology.Singular.Cohomology ℚ P q) => cup P rfl a b)
      (singularCocyclePullback_class (productFirst X Y) p φ).symm
      (singularCocyclePullback_class (productSecond X Y) q ψ).symm

#print axioms tensorScalarCycle_AW_class
end HodgeLean.Foundations.Singular
