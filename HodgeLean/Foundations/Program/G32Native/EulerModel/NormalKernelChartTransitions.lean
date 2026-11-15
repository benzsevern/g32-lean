import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelCoordinateAtlas

/-! # Actual coordinate formulas for the global kernel atlas -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual ambient chart reads precisely the specified permuted affine base and kernel-vector coordinates on its source. -/
theorem normalCoordinateKernelChart_apply (k : ℕ) (j : Fin (k + 1))
    (v : ProjectiveNormalTotalSpace k) (hv : v ∈ (normalCoordinateKernelChart k j).source) :
    normalCoordinateKernelChart k j v =
      (normalProjectiveAffineCoordinate k
          (normalPermutationBaseHomeomorph k (Equiv.swap 0 j) v.1.1),
        (normalCoordinatePermutation k (Equiv.swap 0 j) v.1.2).2) := by
  rw [normalCoordinateKernelChart_source] at hv
  obtain ⟨za, rfl⟩ := hv
  rw [normalCoordinateKernelChart_param]
  simp only [normalCoordinateKernelParam, normalCoordinateKernelChart_value,
    Homeomorph.apply_symm_apply, LinearEquiv.apply_symm_apply,
    normalProjectiveAffineCoordinate_chart, normalKernelChart_val]

#print axioms normalCoordinateKernelChart_apply
/-- The actual change between two specified kernel charts has its exact homogeneous-ratio base and complex-linear fibre formula. -/
theorem normalCoordinateKernelChart_transition (k : ℕ) (i j : Fin (k + 1))
    (za : (Fin k → ℂ) × (Fin k → ℂ))
    (hv : normalCoordinateKernelParam k j za ∈ (normalCoordinateKernelChart k i).source) :
    normalCoordinateKernelChart k i (normalCoordinateKernelParam k j za) =
      (homogeneousNormalChartCoordinate k
        (normalCoordinatePermutation k (Equiv.swap 0 i)
          ((normalCoordinatePermutation k (Equiv.swap 0 j)).symm (1, za.1))),
        (normalCoordinatePermutation k (Equiv.swap 0 i)
          ((normalCoordinatePermutation k (Equiv.swap 0 j)).symm
            (normalKernelChart k za.1 za.2).1)).2) := by
  rw [normalCoordinateKernelChart_apply k i _ hv]
  simp only [normalCoordinateKernelParam, normalCoordinateKernelChart_value]
  unfold normalProjectiveChart
  rw [normalPermutationBaseHomeomorph_symm_mk, normalPermutationBaseHomeomorph_mk,
    normalProjectiveAffineCoordinate_mk]

#print axioms normalCoordinateKernelChart_transition
/-- Membership in the actual target chart retains the nonzero denominator of the specified coordinate change. -/
theorem normalCoordinateKernelChart_transition_ne_zero (k : ℕ) (i j : Fin (k + 1))
    (za : (Fin k → ℂ) × (Fin k → ℂ))
    (hv : normalCoordinateKernelParam k j za ∈ (normalCoordinateKernelChart k i).source) :
    (normalCoordinatePermutation k (Equiv.swap 0 i)
      ((normalCoordinatePermutation k (Equiv.swap 0 j)).symm (1, za.1))).1 ≠ 0 := by
  rw [normalCoordinateKernelChart_source, normalCoordinateKernelParam_range] at hv
  change normalPermutationBaseHomeomorph k (Equiv.swap 0 i)
    ((normalPermutationBaseHomeomorph k (Equiv.swap 0 j)).symm
      (normalProjectiveChart k za.1)) ∈ Set.range (normalProjectiveChart k) at hv
  unfold normalProjectiveChart at hv
  rw [normalPermutationBaseHomeomorph_symm_mk, normalPermutationBaseHomeomorph_mk] at hv
  exact (normalProjectiveChart_range_mk k _ _).mp hv

#print axioms normalCoordinateKernelChart_transition_ne_zero
end HodgeLean.Foundations.Program.G32Native.EulerModel
