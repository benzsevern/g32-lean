import HodgeLean.Foundations.Program.PeriodFibreMarkingDefs

noncomputable section
open CategoryTheory AlgebraicGeometry HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
open scoped TensorProduct
namespace HodgeLean.Foundations.Program


section
variable (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q)
theorem b64e_model_rational_column (l : Λ) :
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  b64e_model_rational Λ F hF Q hQ ((1 : ℚ) ⊗ₜ[ℤ] l) =
    b63g4_column (b5_model Λ F hF Q) (b63g_modelForm Λ F hF Q hQ)
      (b5_periodEquiv Λ F hF Q hQ l) := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  apply (b60b_periodLinearEquiv (b5_model Λ F hF Q)).injective
  change (b60b_periodLinearEquiv (b5_model Λ F hF Q))
    ((b60b_periodLinearEquiv (b5_model Λ F hF Q)).symm
      (b2b_flat _ (b4b_transportForm Λ _ (b5_periodEquiv Λ F hF Q hQ) Q)
        ((1 : ℚ) ⊗ₜ[ℤ] (b5_periodEquiv Λ F hF Q hQ l)))) = _
  rw [LinearEquiv.apply_symm_apply]
  ext k
  simp [b60b_periodLinearEquiv, b63g4_column, b60b_addHomLinearEquiv,
    b2b_flat, b2_bilinToAddHom, b4b_transportForm, b63g_modelForm]
  change (Q l ((b5_periodEquiv Λ F hF Q hQ).symm k) : ℚ) =
    (Q ((b5_periodEquiv Λ F hF Q hQ).symm ((b5_periodEquiv Λ F hF Q hQ) l))
      ((b5_periodEquiv Λ F hF Q hQ).symm k) : ℚ)
  rw [AddEquiv.symm_apply_apply]

theorem b64e_model_rational_form (x y : ℚ ⊗[ℤ] Λ) :
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  polarizationForm (torusCohomology_cupProductOf (b5_model Λ F hF Q))
    (b2_abelian_nondegenerate (b5_model Λ F hF Q) (b63g_modelForm Λ F hF Q hQ)
      (b63g_modelForm_riemann Λ F hF Q hQ))
    (b64e_model_rational Λ F hF Q hQ x) (b64e_model_rational Λ F hF Q hQ y) =
    Q.baseChange ℚ x y := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul q l =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul r k =>
      rw [show q ⊗ₜ[ℤ] l = q • ((1 : ℚ) ⊗ₜ[ℤ] l) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        show r ⊗ₜ[ℤ] k = r • ((1 : ℚ) ⊗ₜ[ℤ] k) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        ]
      simp only [map_smul, LinearMap.smul_apply, b64e_model_rational_column]
      rw [b63g4_polarizationForm_column _ _ (b63g_modelForm_riemann Λ F hF Q hQ)]
      have hform : b63g_modelForm Λ F hF Q hQ
          (b5_periodEquiv Λ F hF Q hQ l) (b5_periodEquiv Λ F hF Q hQ k) = Q l k := by
        change Q ((b5_periodEquiv Λ F hF Q hQ).symm ((b5_periodEquiv Λ F hF Q hQ) l))
          ((b5_periodEquiv Λ F hF Q hQ).symm ((b5_periodEquiv Λ F hF Q hQ) k)) = _
        rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
      rw [hform]
      simp only [LinearMap.BilinForm.baseChange_tmul,
        smul_eq_mul, one_mul, mul_one, mul_assoc, zsmul_eq_mul]

end
end HodgeLean.Foundations.Program
