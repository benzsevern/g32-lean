import HodgeLean.Foundations.QuotientDuality.ProperCycleProductSupport

/-! # Actual normal cohomology coordinates in marked product charts
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Normal projection followed by the original marked chart identifies normal-point cohomology with the literal neighborhood support-complement group.
Source: properCycle_product_support_cohomology_equiv; Hatcher, Algebraic Topology, sections 2.1 and 3.1.
HC no distance; AV milestone no distance. -/
def properCycle_product_chart_support_cohomology_equiv
    (X : TopCat.{0}) (A : Set X) (W : Opens X)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : TopCat.{0}) (y : Y) (e : W ≃ₜ (E × Y))
    (he : ∀ w : W, w.val ∈ A ↔ (e w).2 = y) (n : ℕ) :
    CohomologyWithSupport ℚ Y {y} n ≃ₗ[ℚ]
      RelativeCohomology ℚ (neighborhoodSupportComplementPair (W : Set X) A) n := by
  let p : neighborhoodSupportComplementPair (W : Set X) A ≅
      TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.snd ⁻¹' ({y} : Set Y)ᶜ) :=
    TopPair.isoOfSubset e (fun w => not_congr (he w).symm)
  let C := (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ)
    (ComplexShape.up ℕ) n).mapIso
      (HomologicalComplex.linearDualIso ((relativeChainFunctor ℚ).mapIso p))
  exact (properCycle_product_support_cohomology_equiv E Y {y} n).trans C.toLinearEquiv

example (X : TopCat.{0}) (A : Set X) (W : Opens X)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : TopCat.{0}) (y : Y) (e : W ≃ₜ (E × Y))
    (he : ∀ w : W, w.val ∈ A ↔ (e w).2 = y) (n : ℕ)
    (a : CohomologyWithSupport ℚ Y {y} n) :
    (properCycle_product_chart_support_cohomology_equiv X A W E Y y e he n).symm
      (properCycle_product_chart_support_cohomology_equiv X A W E Y y e he n a) = a :=
  LinearEquiv.symm_apply_apply _ _

end HodgeLean.Foundations.QuotientDuality
