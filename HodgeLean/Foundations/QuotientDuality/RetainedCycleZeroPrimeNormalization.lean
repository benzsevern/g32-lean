import HodgeLean.Foundations.QuotientDuality.RetainedCycleZeroNormalUnit
import HodgeLean.Adapters.NormalConeB4aClassExistsPure
import HodgeLean.Foundations.QuotientDuality.ProperCycleSingletonCohomology

/-! # Normalized prime supported classes in dimension zero

Consumer: RetainedCycleConsumerSteps.lean:42, through RetainedCycleProofs.lean:249.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Every normalized prime class on a zero-dimensional integral projective scheme forgets to the singular cup unit. -/
lemma retained_zero_prime_absolute_unit
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (hdim : TopologicalSpace.dim X.left = 0) (ξ : X.left)
    (a : s2e_supportedClass X (properPrime ξ) 0)
    (ha : a3b4_IsCycleClass X.hom (properPrime ξ) 0 a) :
    s2e_classToAbsolute X (properPrime ξ) 0 a = unit (R := ℚ) (a3b4_an X.hom) := by
  have hne : properPrime ξ ≠ 0 := by
    intro h
    have he := congrArg (fun γ : AlgebraicCycle X.left ℚ => γ ξ) h
    simpa [properPrime] using he
  rw [properCycle_zero_dimension_normalized_absolute X hdim _ hne a ha,
    retained_zero_normal_absolute_unit]
  have hξ := properCycle_zero_dimension_point_eq_generic X hdim ξ
  subst ξ
  simp [properPrime]

end HodgeLean.Foundations.QuotientDuality
