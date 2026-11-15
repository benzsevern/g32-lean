import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalProjectiveScheme

/-! # Ordered coordinate permutations of the actual global kernel family -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual homogeneous evaluation is the ordered coordinate pairing on all coordinates. -/
theorem homogeneousNormalEvaluation_ordered (k : ℕ) (v a : ℂ × (Fin k → ℂ)) :
    homogeneousNormalEvaluation k v a =
      ∑ j : Fin (k + 1), normalHomogeneousCoordinates k v j *
        normalHomogeneousCoordinates k a j := by
  rw [homogeneousNormalEvaluation_apply, Fin.sum_univ_succ]
  rfl

#print axioms homogeneousNormalEvaluation_ordered
/-- The specified index permutation as an actual linear equivalence of the original homogeneous coordinate space. -/
def normalCoordinatePermutation (k : ℕ) (e : Equiv.Perm (Fin (k + 1))) :
    (ℂ × (Fin k → ℂ)) ≃ₗ[ℂ] (ℂ × (Fin k → ℂ)) :=
  ((normalHomogeneousCoordinates k).trans (LinearEquiv.funCongrLeft ℂ ℂ e.symm)).trans
    (normalHomogeneousCoordinates k).symm

#print axioms normalCoordinatePermutation
/-- Every ordered homogeneous coordinate retains the supplied inverse index under the actual permutation. -/
theorem normalCoordinatePermutation_coordinate (k : ℕ)
    (e : Equiv.Perm (Fin (k + 1))) (v : ℂ × (Fin k → ℂ)) (j : Fin (k + 1)) :
    normalHomogeneousCoordinates k (normalCoordinatePermutation k e v) j =
      normalHomogeneousCoordinates k v (e.symm j) := by
  simp only [normalCoordinatePermutation, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]

#print axioms normalCoordinatePermutation_coordinate
/-- Simultaneously permuting the actual homogeneous vectors retains the original evaluation pairing. -/
theorem homogeneousNormalEvaluation_permutation (k : ℕ)
    (e : Equiv.Perm (Fin (k + 1))) (v a : ℂ × (Fin k → ℂ)) :
    homogeneousNormalEvaluation k (normalCoordinatePermutation k e v)
      (normalCoordinatePermutation k e a) = homogeneousNormalEvaluation k v a := by
  rw [homogeneousNormalEvaluation_ordered, homogeneousNormalEvaluation_ordered]
  simp_rw [normalCoordinatePermutation_coordinate]
  exact e.symm.sum_comp (fun j => normalHomogeneousCoordinates k v j *
    normalHomogeneousCoordinates k a j)

#print axioms homogeneousNormalEvaluation_permutation
end HodgeLean.Foundations.Program.G32Native.EulerModel
