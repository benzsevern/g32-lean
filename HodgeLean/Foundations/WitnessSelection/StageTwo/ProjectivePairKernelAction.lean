import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairProjectiveKernel

/-! The image of a normalized Hermitian kernel is its representative line.

HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.WitnessSelection.StageTwo

/-- Applying the coordinate kernel gives a scalar multiple of its defining vector.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_projectiveKernel_action {ι : Type*} [Fintype ι]
    (v w : ι → ℂ) (i : ι) :
    (∑ j, s2e_pair_projectiveKernel v i j * w j) =
      ((∑ j, star (v j) * w j) / (s2e_pair_vectorMass v : ℂ)) * v i := by
  rw [Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  change (v i * star (v j) / (s2e_pair_vectorMass v : ℂ)) * w j = _
  ring

end HodgeLean.WitnessSelection.StageTwo
