import HodgeLean.Foundations.Abdulali.OrthogonalReflectionDeterminant
import Mathlib.Tactic.LinearCombination

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Abdulali
open Matrix
variable {n : ℕ}

/-- A reflection takes one vector to another of equal square length whenever
their difference is nonisotropic. This is the vector reduction used in
reflection generation of the orthogonal group.
Source: Weyl, The Classical Groups, Chapter II, §9, orthogonal reflections. -/
theorem orthogonalReflectionMatrix_maps_equal_norm
    (u v : Fin n → ℂ) (hn : u ⬝ᵥ u = v ⬝ᵥ v)
    (huv : (u - v) ⬝ᵥ (u - v) ≠ 0) :
    orthogonalReflectionMatrix (u - v) *ᵥ u = v := by
  have hq : (u - v) ⬝ᵥ (u - v) = 2 * ((u - v) ⬝ᵥ u) := by
    simp only [sub_dotProduct, dotProduct_sub]
    rw [dotProduct_comm v u, ← hn]
    ring
  rw [orthogonalReflectionMatrix, sub_mulVec, one_mulVec,
    smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [huv]
  linear_combination (u i - v i) * hq

/-- Reflection negates its defining nonisotropic vector.
Source: Weyl, The Classical Groups, Chapter II, §9, orthogonal reflections. -/
theorem orthogonalReflectionMatrix_mulVec_self
    (u : Fin n → ℂ) (hu : u ⬝ᵥ u ≠ 0) :
    orthogonalReflectionMatrix u *ᵥ u = -u := by
  rw [orthogonalReflectionMatrix, sub_mulVec, one_mulVec,
    smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  field_simp [hu]
  <;> ring

#print axioms orthogonalReflectionMatrix_maps_equal_norm
#print axioms orthogonalReflectionMatrix_mulVec_self
end HodgeLean.Foundations.Abdulali
