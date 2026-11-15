import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalPermutationBase

/-! # Exact identity of the leading actual kernel coordinate permutation -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The specified leading coordinate permutation retains every original homogeneous vector. -/
theorem normalCoordinatePermutation_swap_zero (k : ℕ) (v : ℂ × (Fin k → ℂ)) :
    normalCoordinatePermutation k (Equiv.swap 0 0) v = v := by
  apply (normalHomogeneousCoordinates k).injective
  ext j
  rw [normalCoordinatePermutation_coordinate]
  simp

#print axioms normalCoordinatePermutation_swap_zero
/-- The leading actual projective kernel coordinate action retains every original base point. -/
theorem normalPermutationBaseHomeomorph_swap_zero (k : ℕ)
    (p : Projectivization ℂ (ℂ × (Fin k → ℂ))) :
    normalPermutationBaseHomeomorph k (Equiv.swap 0 0) p = p := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [normalPermutationBaseHomeomorph_mk]
    simp only [normalCoordinatePermutation_swap_zero]

#print axioms normalPermutationBaseHomeomorph_swap_zero
end HodgeLean.Foundations.Program.G32Native.EulerModel
