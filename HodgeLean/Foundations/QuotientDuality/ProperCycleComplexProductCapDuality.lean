import HodgeLean.Foundations.QuotientDuality.ProperCycleVectorCapDuality

/-! # The specified normal cap on actual complex product coordinates -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original standard complex normal coclass, pulled back by the literal normal projection, gives bijectivity of the original cap in the actual complex tangential product.
Source: Hatcher, Algebraic Topology, section 3.3, complex normal cap duality.
HC no distance; AV milestone no distance. -/
lemma properCycle_standard_complex_product_triad_cap_bijective (r d : ℕ) :
    let E := Fin r → ℂ
    let Y := TopCat.of (Fin d → ℂ)
    Function.Bijective (triadCapCohomologyLinear ℚ (TopCat.of (E × Y))
      (Prod.snd ⁻¹' ({0} : Set Y)ᶜ) {z | z.1 = 0}ᶜ (2 * d) (2 * r)
      (relativeCohomologyMap ℚ (2 * d) (properCycle_product_support_projection E Y {0})
        (normalizedRelativeCoclass (standardComplexLocalClass ℚ d)
          (standardComplexLocalClass_ne_zero_for_chart d)))) := by
  dsimp only
  have h := properCycle_vector_product_cap_bijective (Fin r → ℂ) (TopCat.of (Fin d → ℂ))
    {0} Set.univ isClosed_singleton isClosed_univ (2 * d) 0 (by exact ⟨d, by omega⟩)
    (normalizedRelativeCoclass (standardComplexLocalClass ℚ d)
      (standardComplexLocalClass_ne_zero_for_chart d))
    (by rw [Set.compl_univ]; exact properCycle_standard_normal_triad_cap_bijective d)
  have hdim : Module.finrank ℝ (Fin r → ℂ) = 2 * r := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (Fin r → ℂ), Complex.finrank_real_complex,
      Module.finrank_pi, Fintype.card_fin]
  rw [Nat.zero_add, hdim] at h
  have hB : {z : (Fin r → ℂ) × (Fin d → ℂ) | z.1 = 0 ∧ z.2 ∈ (Set.univ : Set (Fin d → ℂ))}ᶜ =
      {z | z.1 = 0}ᶜ := by ext z; simp
  rw [hB] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
