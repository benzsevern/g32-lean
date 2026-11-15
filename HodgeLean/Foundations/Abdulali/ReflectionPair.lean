import HodgeLean.Foundations.Abdulali.OrthogonalReflectionDeterminant
import HodgeLean.Foundations.Abdulali.SpecialOrthogonalLie

noncomputable section
set_option maxHeartbeats 200000
set_option Elab.async false
namespace HodgeLean.Foundations.Abdulali
open HodgeLean.Foundations
variable {n : ℕ}

/-- The product of two actual orthogonal reflections is an element of the
actual determinant-one isometry matrix group.
Source: Weyl, The Classical Groups, Chapter II, §9, orthogonal reflections. -/
theorem reflection_pair_mem_specialOrthogonal
    (u v : Fin n → ℂ) (hu : u ⬝ᵥ u ≠ 0) (hv : v ⬝ᵥ v ≠ 0) :
    orthogonalReflectionGL u hu * orthogonalReflectionGL v hv ∈
      (specialOrthogonalMatrixGroup (1 : Matrix (Fin n) (Fin n) ℂ)).carrier := by
  have hr (w : Fin n → ℂ) (hw : w ⬝ᵥ w ≠ 0) :
      orthogonalReflectionGL w hw ∈
        (g1_isometryGroup (1 : Matrix (Fin n) (Fin n) ℂ)).carrier := by
    change (orthogonalReflectionMatrix w).transpose * 1 * orthogonalReflectionMatrix w = 1
    exact orthogonalReflectionMatrix_isometry w hw
  have hm := (g1_isometryGroup (1 : Matrix (Fin n) (Fin n) ℂ)).carrier.mul_mem
    (hr u hu) (hr v hv)
  rw [mem_specialOrthogonalMatrixGroup]
  constructor
  · exact hm
  · change (orthogonalReflectionMatrix u * orthogonalReflectionMatrix v).det = 1
    rw [Matrix.det_mul, orthogonalReflectionMatrix_det u hu,
      orthogonalReflectionMatrix_det v hv]
    ring

#print axioms reflection_pair_mem_specialOrthogonal
end HodgeLean.Foundations.Abdulali
