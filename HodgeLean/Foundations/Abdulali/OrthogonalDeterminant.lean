import HodgeLean.Foundations.Abdulali.QuaternionInvolution
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.BilinearForm

noncomputable section
namespace HodgeLean.Foundations.Abdulali

/-- The determinant character of a nondegenerate bilinear isometry has order
at most two. This retains the determinant restriction separating O from SO.
Symmetry is not needed for this calculation.
Source: Weyl, The Classical Groups, Chapter II, §9. -/
theorem orthogonal_determinant_sq (d : ℕ)
    (B : LinearMap.BilinForm ℂ (Fin d → ℂ)) (hB : B.Nondegenerate)
    (u : Module.End ℂ (Fin d → ℂ))
    (hu : ∀ x y, B (u x) (u y) = B x y) : u.det ^ 2 = 1 := by
  let Q := LinearMap.toMatrix₂' ℂ B
  have hQ : Q.det ≠ 0 := by
    apply LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mp
    simpa [Q] using hB
  have hform : B.compl₁₂ u u = B := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact hu x y
  have hm := congrArg (LinearMap.toMatrix₂' ℂ) hform
  rw [LinearMap.toMatrix₂'_compl₁₂] at hm
  have hdet := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    LinearMap.det_toMatrix'] at hdet
  have h : u.det ^ 2 * Q.det = 1 * Q.det := by
    change _ = _ at hdet
    calc _ = u.det * Q.det * u.det := by ring
         _ = Q.det := hdet
         _ = _ := by rw [one_mul]
  exact mul_right_cancel₀ hQ h

/-- Over ℂ the orthogonal determinant character takes exactly the possible
values `1` and `-1`, with no assertion that both values occur in dimension zero.
Source: Weyl, The Classical Groups, Chapter II, §9. -/
theorem orthogonal_determinant_cases (d : ℕ)
    (B : LinearMap.BilinForm ℂ (Fin d → ℂ)) (hB : B.Nondegenerate)
    (u : Module.End ℂ (Fin d → ℂ))
    (hu : ∀ x y, B (u x) (u y) = B x y) : u.det = 1 ∨ u.det = -1 := by
  have h := orthogonal_determinant_sq d B hB u hu
  exact (sq_eq_one_iff).mp h

end HodgeLean.Foundations.Abdulali
