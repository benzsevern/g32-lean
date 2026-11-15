import HodgeLean.Foundations.QuotientDuality.ProperCycleLinearExtension
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.Purity

/-! # Normalized relative coclasses from actual homology lines -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The canonical coclass normalized on an actual relative homology generator generates cohomology.
Source: Hatcher, Algebraic Topology, section 3.1, universal coefficients over a field.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_normalized_generator (P : TopPair.{0}) (n : ℕ)
    (z : RelativeHomology ℚ P n)
    (hgen : Function.Bijective (LinearMap.toSpanSingleton ℚ (RelativeHomology ℚ P n) z)) :
    ∃ α : RelativeCohomology ℚ P n,
      relativeCohomologyEquivDualHomology ℚ P n α z = 1 ∧
      Function.Bijective (LinearMap.toSpanSingleton ℚ (RelativeCohomology ℚ P n) α) := by
  have hz : z ≠ 0 := by
    intro hz
    exact (one_ne_zero : (1 : ℚ) ≠ 0) (hgen.1 (by simp [hz]))
  let α := normalizedRelativeCoclass z hz
  have hα : relativeCohomologyEquivDualHomology ℚ P n α z = 1 :=
    normalizedRelativeCoclass_pairing_self z hz
  refine ⟨α, hα, ?_, ?_⟩
  · intro p q hpq
    have h := congrArg (fun β : RelativeCohomology ℚ P n =>
      relativeCohomologyEquivDualHomology ℚ P n β z) hpq
    change relativeCohomologyEquivDualHomology ℚ P n (p • α) z =
      relativeCohomologyEquivDualHomology ℚ P n (q • α) z at h
    simpa only [map_smul, LinearMap.smul_apply, hα, smul_eq_mul, mul_one] using h
  · intro β
    let q := relativeCohomologyEquivDualHomology ℚ P n β z
    obtain ⟨F, hF, huniq⟩ := properCycle_linear_extension_unique z q hgen
    refine ⟨q, ?_⟩
    apply (relativeCohomologyEquivDualHomology ℚ P n).injective
    change relativeCohomologyEquivDualHomology ℚ P n (q • α) =
      relativeCohomologyEquivDualHomology ℚ P n β
    have hqa : relativeCohomologyEquivDualHomology ℚ P n (q • α) z = q := by
      rw [map_smul, LinearMap.smul_apply, hα, smul_eq_mul, mul_one]
    exact (huniq _ hqa).trans (huniq _ rfl).symm

end HodgeLean.Foundations.QuotientDuality
