import HodgeLean.Foundations.Program.G32ContractionProjection
import HodgeLean.RealDefs.CupFiltered

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option Elab.async false

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

theorem g32c_corrC_tmul (Y B : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (c p q : ℕ)
    (h : 2 * c + 2 * p = 2 * q + 2 * d)
    (z v : ℂ) (ξ : HQ (Y ⊗ B) (2 * c)) (x : HQ B (2 * p)) :
    g32c_corrC Y B d I c p q h (z ⊗ₜ ξ) (v ⊗ₜ x) =
      (z * v) ⊗ₜ cfd_corrAction Y B d I c p q h ξ x := by
  simp only [g32c_corrC, TensorProduct.curry_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
    LinearMap.baseChange_tmul, TensorProduct.lift.tmul]
  rfl


theorem g32c_contraction_crossC (Y B : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hB : TopologicalSpace.dim B.left = d) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ)
    (c p q e : ℕ) (h : 2 * c + 2 * p = 2 * q + 2 * d) (hc : 2 * q + 2 * e = 2 * c)
    (hd : 2 * e + 2 * p = 2 * d)
    (a : ℂ ⊗[ℚ] HQ Y (2 * q)) (b : ℂ ⊗[ℚ] HQ B (2 * e))
    (x : ℂ ⊗[ℚ] HQ B (2 * p)) :
    g32c_corrC Y B d I c p q h
      ((cupProductOf (Y ⊗ B)).cupC hc
        ((homPullback (fst Y B) (2 * q)).baseChange ℂ a)
        ((homPullback (snd Y B) (2 * e)).baseChange ℂ b)) x =
      TensorProduct.AlgebraTensorModule.rid ℚ ℂ ℂ
        (I.toLinearMap.baseChange ℂ ((cupProductOf B).cupC hd b x)) • a := by
  induction a using TensorProduct.inductionOn with
  | add a a' ha ha' =>
      simp only [map_add, LinearMap.add_apply, ha, ha', smul_add]
  | tmul z a =>
      induction b using TensorProduct.inductionOn with
      | add b b' hb hb' =>
          simp only [map_add, LinearMap.add_apply, hb, hb', add_smul]
      | tmul v b =>
          induction x using TensorProduct.inductionOn with
          | add x x' hx hx' => simp only [map_add, hx, hx', add_smul]
          | tmul u x =>
              rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
                CupProduct.cupC_tmul, g32c_corrC_tmul,
                g32c_contraction_tensor Y B d hB I c p q e h hc hd,
                CupProduct.cupC_tmul, LinearMap.baseChange_tmul,
                TensorProduct.AlgebraTensorModule.rid_tmul]
              simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul',
                smul_eq_mul, Rat.smul_def]
              congr 1
              change (I ((cupProductOf B).cup hd b x) : ℂ) * (z * v * u) =
                (I ((cupProductOf B).cup hd b x) : ℂ) * (v * u) * z
              ring

end HodgeLean.Foundations.Program
