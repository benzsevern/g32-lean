import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalCoordinateKernelDomains
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalPermutationTotalSpace

/-! # Actual kernel coordinates on every projective coordinate open -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The specified coordinate action identifies its actual kernel domain with the original leading-coordinate domain. -/
def normalPermutationChartDomainHomeomorph (k : ℕ) (j : Fin (k + 1)) :
    NormalCoordinateKernelDomain k j ≃ₜ NormalKernelChartDomain k := by
  let A := normalPermutationTotalHomeomorph k (Equiv.swap 0 j)
  have hi (v : NormalKernelChartDomain k) :
      normalPermutationBaseHomeomorph k (Equiv.swap 0 j) (A.symm v.1).1.1 ∈
        Set.range (normalProjectiveChart k) := by
    change (A (A.symm v.1)).1.1 ∈ Set.range (normalProjectiveChart k)
    rw [A.apply_symm_apply]
    exact v.2
  exact
    { toFun := fun v => ⟨A v.1, v.2⟩
      invFun := fun v => ⟨A.symm v.1, hi v⟩
      left_inv := fun v => Subtype.ext (A.symm_apply_apply v.1)
      right_inv := fun v => Subtype.ext (A.apply_symm_apply v.1)
      continuous_toFun := (A.continuous.comp continuous_subtype_val).subtype_mk (fun v => v.2)
      continuous_invFun := (A.symm.continuous.comp continuous_subtype_val).subtype_mk hi }

#print axioms normalPermutationChartDomainHomeomorph
/-- Every specified coordinate kernel domain has its actual ordered base and fibre product coordinates. -/
def normalCoordinateKernelChartHomeomorph (k : ℕ) (j : Fin (k + 1)) :
    NormalCoordinateKernelDomain k j ≃ₜ ((Fin k → ℂ) × (Fin k → ℂ)) :=
  (normalPermutationChartDomainHomeomorph k j).trans (normalKernelTotalChartHomeomorph k).symm

#print axioms normalCoordinateKernelChartHomeomorph
/-- The actual chart inverse retains its specified projective base and complex-linear kernel vector. -/
theorem normalCoordinateKernelChart_value (k : ℕ) (j : Fin (k + 1))
    (za : (Fin k → ℂ) × (Fin k → ℂ)) :
    ((normalCoordinateKernelChartHomeomorph k j).symm za).1.1 =
      ((normalPermutationBaseHomeomorph k (Equiv.swap 0 j)).symm
          (normalProjectiveChart k za.1),
        (normalCoordinatePermutation k (Equiv.swap 0 j)).symm
          (normalKernelChart k za.1 za.2).1) := rfl

#print axioms normalCoordinateKernelChart_value
/-- Every specified actual kernel chart retains the zero vector exactly as the zero fibre coordinate. -/
theorem normalCoordinateKernelChart_vector_zero_iff (k : ℕ) (j : Fin (k + 1))
    (za : (Fin k → ℂ) × (Fin k → ℂ)) :
    ((normalCoordinateKernelChartHomeomorph k j).symm za).1.1.2 = 0 ↔ za.2 = 0 := by
  rw [normalCoordinateKernelChart_value]
  change (normalCoordinatePermutation k (Equiv.swap 0 j)).symm
    (normalKernelChart k za.1 za.2).1 = 0 ↔ za.2 = 0
  rw [LinearEquiv.map_eq_zero_iff]
  exact normalKernelTotalChart_vector_zero_iff k za

#print axioms normalCoordinateKernelChart_vector_zero_iff
end HodgeLean.Foundations.Program.G32Native.EulerModel
