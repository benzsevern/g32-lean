import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairKernelSelf

/-! Normalized Hermitian kernels distinguish complex projective lines.

HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.WitnessSelection.StageTwo

/-- Equality of normalized kernels is exactly nonzero scalar equivalence.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_projectiveKernel_eq_iff_smul {ι : Type*} [Fintype ι]
    (v : ι → ℂ) (hv : v ≠ 0) (w : ι → ℂ) :
    s2e_pair_projectiveKernel v = s2e_pair_projectiveKernel w ↔
      ∃ c : ℂ, c ≠ 0 ∧ c • w = v := by
  constructor
  · intro he
    let c : ℂ := (∑ j, star (w j) * v j) / (s2e_pair_vectorMass w : ℂ)
    have hcv : c • w = v := by
      funext i
      have h := s2e_pair_projectiveKernel_self v hv i
      rw [he, s2e_pair_projectiveKernel_action] at h
      exact h
    have hc : c ≠ 0 := by
      intro hz
      apply hv
      rw [← hcv, hz, zero_smul]
    exact ⟨c, hc, hcv⟩
  · rintro ⟨c, hc, rfl⟩
    exact s2e_pair_projectiveKernel_smul c hc w

end HodgeLean.WitnessSelection.StageTwo
