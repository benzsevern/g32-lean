import HodgeLean.Foundations.Program.MilneTensorAdjointNormOne
import HodgeLean.Foundations.Program.MilneTensorMatrixAlternating

noncomputable section
namespace HodgeLean.Foundations.Program

theorem m1b_gramAdjoint_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B X : Matrix ι ι ℂ) (hB : IsUnit B) (x y : ι → ℂ) :
    B.toBilin' (X.mulVec x) y =
      B.toBilin' x ((B⁻¹ * X.transpose * B).mulVec y) := by
  have hBB : B * (B⁻¹ * X.transpose * B) = X.transpose * B := by
    rw [← mul_assoc, ← mul_assoc, B.mul_nonsing_inv (hB.map Matrix.detMonoidHom), one_mul]
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.mulVec_mulVec, hBB]
  calc
    (X.mulVec x) ⬝ᵥ (B.mulVec y) = (B.mulVec y) ⬝ᵥ (X.mulVec x) := dotProduct_comm _ _
    _ = x ⬝ᵥ (X.transpose.mulVec (B.mulVec y)) :=
      (Matrix.dotProduct_transpose_mulVec X x (B.mulVec y)).symm
    _ = x ⬝ᵥ ((X.transpose * B).mulVec y) := by rw [Matrix.mulVec_mulVec]

theorem m1b_gram_norm_one_image (d : ℕ) (B : Matrix (Fin d) (Fin d) ℂ)
    (hB : IsUnit B) :
    Matrix.toLin' '' {X | m1_gramAdjoint d B X * X = 1} =
      m1b_isometries B.toBilin' := by
  let e : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin d → ℂ) :=
    Matrix.toLinAlgEquiv'
  let τ : Module.End ℂ (Fin d → ℂ) → Module.End ℂ (Fin d → ℂ) :=
    fun u => e (m1_gramAdjoint d B (e.symm u))
  have hadj (u : Module.End ℂ (Fin d → ℂ)) (x y : Fin d → ℂ) :
      B.toBilin' (u x) y = B.toBilin' x (τ u y) := by
    have h := m1b_gramAdjoint_pair B (e.symm u) hB x y
    change B.toBilin' (e (e.symm u) x) y = B.toBilin' x (τ u y) at h
    simpa only [e.apply_symm_apply] using h
  rw [← m1b_adjoint_norm_one_set B.toBilin'
    (LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr
      (hB.map Matrix.detMonoidHom).ne_zero) τ hadj]
  ext u
  constructor
  · rintro ⟨X, hX, rfl⟩
    change e (m1_gramAdjoint d B (e.symm (e X))) * e X = 1
    rw [e.symm_apply_apply, ← map_mul, hX, map_one]
  · intro hu
    refine ⟨e.symm u, ?_, e.apply_symm_apply u⟩
    apply e.injective
    rw [map_mul, map_one]
    change τ u * e (e.symm u) = 1
    rwa [e.apply_symm_apply]

end HodgeLean.Foundations.Program
