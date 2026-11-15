import HodgeLean.Foundations.QuotientDuality.ProperCycleZeroAbsoluteNormalization
import HodgeLean.Foundations.QuotientDuality.ProperCycleSingletonCohomology
import HodgeLean.Adapters.NormalConeB4aClassExistsPure

/-! # Supported detection and cycle normalization in dimension zero

Consumer: RetainedCycleConsumerSteps.lean:42, through RetainedCycleProofs.lean:249.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- On a zero-dimensional integral projective scheme, forgetting the support of any nonzero cycle is injective in every cycle-class degree. -/
lemma retained_zero_cycle_absolute_injective
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (hdim : TopologicalSpace.dim X.left = 0)
    (γ : AlgebraicCycle X.left ℚ) (hγ : γ ≠ 0) (k : ℕ) :
    Function.Injective (s2e_classToAbsolute X γ k) := by
  change Function.Injective (forgetSupport ℚ (a3b4_an X.hom)
    (a3b4_cycleSupport X.hom γ) (2*k))
  rw [properCycle_zero_dimension_nonzero_support X hdim γ hγ]
  exact (wholeSupportCohomologyLinearEquiv ℚ (a3b4_an X.hom) (2*k)).injective

/-- Every rational cycle on a zero-dimensional integral projective scheme has exactly one normalized supported class. -/
lemma retained_zero_cycle_normalized_unique
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (hdim : TopologicalSpace.dim X.left = 0)
    (γ : AlgebraicCycle X.left ℚ) :
    ∃! a : s2e_supportedClass X γ 0, a3b4_IsCycleClass X.hom γ 0 a := by
  by_cases hγ : γ = 0
  · subst γ
    exact ⟨0, properCycle_zero_normalized X 0,
      fun b _ => properCycle_zero_supported_eq_zero X 0 b⟩
  · letI : Smooth X.hom := properCycle_zero_dimension_smooth X hdim
    obtain ⟨a, ha⟩ := a3b4a_cycleClass_exists_of_codimension X.hom γ 0 (fun _ _ => bot_le)
    refine ⟨a, ha, fun b hb => retained_zero_cycle_absolute_injective X hdim γ hγ 0 ?_⟩
    rw [properCycle_zero_dimension_normalized_absolute X hdim γ hγ b hb,
      properCycle_zero_dimension_normalized_absolute X hdim γ hγ a ha]

end HodgeLean.Foundations.QuotientDuality
