import HodgeLean.Foundations.Program.G32SelectedRealizationMusicalAdjoint

noncomputable section
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open scoped TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program

theorem g32y_model_comparison_adjoint (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (J K : Λ →+ Λ)
    (hAdj : ∀ x y, Q (J x) y = Q x (K y)) (x : ℂ ⊗[ℤ] Λ) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
    letI := b5_smooth Λ F hF Q hQ
    letI := b5_projective Λ F hF Q hQ
    b64d_model_homologyCohomology Λ F hF Q hQ (b2_cplxMap J x) =
      (b4b_cohomologyAction Λ (b5_model Λ F hF Q) (b5_periodEquiv Λ F hF Q hQ) K).baseChange ℂ
        (b64d_model_homologyCohomology Λ F hF Q hQ x) := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  let X := b5_model Λ F hF Q
  let e := b5_periodEquiv Λ F hF Q hQ
  let R := b4b_transportForm Λ X e Q
  let em := LinearEquiv.baseChange ℤ ℂ _ _ e.toIntLinearEquiv
  let ep := LinearEquiv.baseChange ℚ ℂ _ _ (b60b_periodLinearEquiv X)
  let A := b4b_cohomologyAction Λ X e K
  let CJ := e.toAddMonoidHom.comp (J.comp e.symm.toAddMonoidHom)
  let CK := e.toAddMonoidHom.comp (K.comp e.symm.toAddMonoidHom)
  have hmark (z : ℂ ⊗[ℤ] Λ) :
      em (b2_cplxMap J z) = b2_cplxMap CJ (em z) := by
    induction z using TensorProduct.inductionOn with
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul c u =>
      simp only [em, b2_cplxMap, LinearMap.baseChange_tmul,
        LinearEquiv.baseChange_tmul]
      congr 1
      change e (J u) = e (J (e.symm (e u)))
      rw [e.symm_apply_apply]
  have hR (u v : b2_abelianLattice X) : R (CJ u) v = R u (CK v) := by
    change Q (e.symm (e (J (e.symm u)))) (e.symm v) =
      Q (e.symm u) (e.symm (e (K (e.symm v))))
    rw [e.symm_apply_apply, e.symm_apply_apply]
    exact hAdj _ _
  have hperiod (z : ℂ ⊗[ℚ] HQ X 1) :
      ep (A.baseChange ℂ z) =
        (b60b_dualPrecomp CK).baseChange ℂ (ep z) := by
    induction z using TensorProduct.inductionOn with
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul c u =>
      rw [LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul,
        LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul]
      congr 1
      ext l
      change abelianPeriodEquiv X (A u) l =
        abelianPeriodEquiv X u (e (K (e.symm l)))
      dsimp only [A, b4b_cohomologyAction]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply]
      rfl
  have hep (z : ℂ ⊗[ℚ] b2b_dual (b2_abelianLattice X)) :
      ep.symm ((b60b_dualPrecomp CK).baseChange ℂ z) =
        A.baseChange ℂ (ep.symm z) := by
    apply ep.injective
    rw [ep.apply_symm_apply, hperiod, ep.apply_symm_apply]
  change ep.symm (b2bpol_musical _ R (em (b2_cplxMap J x))) =
    A.baseChange ℂ (ep.symm (b2bpol_musical _ R (em x)))
  rw [hmark, g32y_musical_adjoint R CJ CK hR, hep]

end HodgeLean.Foundations.Program
