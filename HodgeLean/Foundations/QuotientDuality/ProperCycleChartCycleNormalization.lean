import HodgeLean.Foundations.QuotientDuality.ProperCycleChartCoclassComparison
import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs

/-! # Original normalized cycle classes in the actual product support cap diagram -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicTopology AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The original cycle-class normalization supplies an actual neighborhood on which the original class is the literal chart pullback of its multiplicity times the specified projected standard normal coclass.
Source: Fulton, Intersection Theory, section 19.1, local normalization of cycle classes.
HC no distance; AV milestone no distance. -/
lemma properCycle_normalized_chart_class_product
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (k : ℕ) (a : s2e_supportedClass X γ k)
    (ha : a3b4_IsCycleClass X.hom γ k a) (r : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
    (hS : ∀ z ∈ e.source, z ∈ a3b4_cycleSupport X.hom γ ↔ (e z).2 = 0)
    (he : a3b4_IsHolChart X.hom e) (x : ComplexPoint X) (hx : x ∈ e.source)
    (hxS : x ∈ a3b4_cycleSupport X.hom γ) :
    ∃ (W : Set (ComplexPoint X)) (hW : W ⊆ e.source), IsOpen W ∧ x ∈ W ∧
      relativeCohomologyMap ℚ (2 * k)
        (a3b4_neighborhoodPairMap W (a3b4_cycleSupport X.hom γ)) a =
      relativeCohomologyMap ℚ (2 * k)
        (properCycle_chart_normal_support_pair_map (M := a3b4_an X.hom) (Fin r → ℂ) k e
          (a3b4_cycleSupport X.hom γ) hS W hW)
        (a3b4_multiplicity X.hom γ x • relativeCohomologyMap ℚ (2 * k)
          (properCycle_product_support_projection (Fin r → ℂ) (TopCat.of (Fin k → ℂ)) {0})
          (normalizedRelativeCoclass (standardComplexLocalClass ℚ k)
            (standardComplexLocalClass_ne_zero_for_chart k))) := by
  obtain ⟨W, hW, hWo, hxW, hWa⟩ := ha r e hS x hx hxS he
  refine ⟨W, hW, hWo, hxW, ?_⟩
  rw [map_smul, properCycle_chart_normal_coclass_product (M := a3b4_an X.hom)]
  exact hWa

end HodgeLean.Foundations.QuotientDuality
