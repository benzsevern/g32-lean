import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairProjectiveMass

/-! Scale-invariant Hermitian coordinate kernels.

HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.WitnessSelection.StageTwo

/-- The normalized rank-one Hermitian matrix of a coordinate vector.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
def s2e_pair_projectiveKernel {ι : Type*} [Fintype ι] (v : ι → ℂ) : ι → ι → ℂ :=
  fun i j => v i * star (v j) / (s2e_pair_vectorMass v : ℂ)

/-- Nonzero rescaling preserves the normalized Hermitian kernel.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_projectiveKernel_smul {ι : Type*} [Fintype ι]
    (c : ℂ) (hc : c ≠ 0) (v : ι → ℂ) :
    s2e_pair_projectiveKernel (c • v) = s2e_pair_projectiveKernel v := by
  funext i j
  change (c * v i) * star (c * v j) / (s2e_pair_vectorMass (c • v) : ℂ) = _
  rw [s2e_pair_vectorMass_smul, Complex.ofReal_mul, ← Complex.mul_conj c]
  rw [star_mul, mul_comm (star (v j)) (star c)]
  change (c * v i) * (star c * star (v j)) /
    ((c * star c) * (s2e_pair_vectorMass v : ℂ)) = _
  have hnum : (c * v i) * (star c * star (v j)) =
      (c * star c) * (v i * star (v j)) := by ring
  rw [hnum, mul_div_mul_left _ _ (mul_ne_zero hc (by simpa only [star_ne_zero] using hc))]
  rfl

end HodgeLean.WitnessSelection.StageTwo
