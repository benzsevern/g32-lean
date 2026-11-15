import HodgeLean.Foundations.Program.PeriodComparisonModelDefs

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

theorem b64d_model_homologyCohomology_F_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
    letI := b5_smooth Λ F hF Q hQ
    letI := b5_projective Λ F hF Q hQ
    F.map (b64d_model_homologyCohomology Λ F hF Q hQ).toLinearMap = cohomologyHodgePiece (b5_model Λ F hF Q) 1 (1, 0) := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  let X := b5_model Λ F hF Q
  let e := b5_periodEquiv Λ F hF Q hQ
  let R := b4b_transportForm Λ X e Q
  let hR := b4b_transportForm_riemann_aux Λ X e F
    (b5_period_filtration Λ F hF Q hQ) Q hQ
  let em := LinearEquiv.baseChange ℤ ℂ _ _ e.toIntLinearEquiv
  let hflat := b2bpol_flat_bijective (b2_abelianLattice X) R
    (fun u hu ↦ b2_riemannForm_nondegenerate (b2_abelianF X)
      R (b2_abelianF_isWeightOne X)
      hR u hu)
  let emus := LinearEquiv.ofBijective
    (b2bpol_musical (b2_abelianLattice X) R)
    (b2bpol_musical_bijective (b2_abelianLattice X) R hflat)
  let ep := LinearEquiv.baseChange ℚ ℂ _ _ (b60b_periodLinearEquiv X)
  rw [show b64d_model_homologyCohomology Λ F hF Q hQ = em.trans (emus.trans ep.symm) by rfl]
  change F.map
    (ep.symm.toLinearMap.comp (emus.toLinearMap.comp em.toLinearMap)) = _
  rw [Submodule.map_comp, Submodule.map_comp]
  change ((F.map em.toLinearMap).map emus.toLinearMap).map
    ep.symm.toLinearMap = _
  have hmark : F.map em.toLinearMap = b2_abelianF X := by
    change F.map (b2_cplxMap e.toAddMonoidHom) = _
    exact b5_period_filtration Λ F hF Q hQ
  rw [hmark]
  have hmus := b2bpol_hodgeOne_eq_map (b2_abelianLattice X)
    (b2_abelianF X) R
    (b2_abelianF_isWeightOne X) hR hflat
  change ((b2_abelianF X).map
    (b2bpol_musical (b2_abelianLattice X) R)).map
      ep.symm.toLinearMap = _
  rw [← hmus]
  have hp := b60b_h10_period X
  change (cohomologyHodgePiece X 1 (1, 0)).map ep.toLinearMap = _ at hp
  rw [← hp, ← Submodule.map_comp]
  have hc : ep.symm.toLinearMap.comp ep.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact ep.symm_apply_apply x
  rw [hc, Submodule.map_id]

theorem b64d_model_homologyCohomology_intertwines_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (J : Λ →+ Λ)
    (hskew : ∀ x y, Q (J x) y = -Q x (J y)) (x : ℂ ⊗[ℤ] Λ) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
    letI := b5_smooth Λ F hF Q hQ
    letI := b5_projective Λ F hF Q hQ
    b64d_model_homologyCohomology Λ F hF Q hQ (b2_cplxMap J x) =
      -(b4b_cohomologyAction Λ (b5_model Λ F hF Q) (b5_periodEquiv Λ F hF Q hQ) J).baseChange ℂ
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
  let A := b4b_cohomologyAction Λ X e J
  let K := e.toAddMonoidHom.comp (J.comp e.symm.toAddMonoidHom)
  have hmark (z : ℂ ⊗[ℤ] Λ) :
      em (b2_cplxMap J z) = b2_cplxMap K (em z) := by
    induction z using TensorProduct.inductionOn with
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul c u =>
      simp only [em, b2_cplxMap, LinearMap.baseChange_tmul,
        LinearEquiv.baseChange_tmul]
      congr 1
      change e (J u) = e (J (e.symm (e u)))
      rw [e.symm_apply_apply]
  have hRskew (u v : b2_abelianLattice X) : R (K u) v = -R u (K v) := by
    change Q (e.symm (e (J (e.symm u)))) (e.symm v) =
      -Q (e.symm u) (e.symm (e (J (e.symm v))))
    rw [e.symm_apply_apply, e.symm_apply_apply]
    exact hskew _ _
  have hperiod (z : ℂ ⊗[ℚ] HQ X 1) :
      ep (A.baseChange ℂ z) =
        (b60b_dualPrecomp K).baseChange ℂ (ep z) := by
    induction z using TensorProduct.inductionOn with
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul c u =>
      rw [LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul,
        LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul]
      congr 1
      ext l
      change abelianPeriodEquiv X (A u) l =
        abelianPeriodEquiv X u (e (J (e.symm l)))
      dsimp only [A, b4b_cohomologyAction]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply]
      rfl
  have hep (z : ℂ ⊗[ℚ] b2b_dual (b2_abelianLattice X)) :
      ep.symm ((b60b_dualPrecomp K).baseChange ℂ z) =
        A.baseChange ℂ (ep.symm z) := by
    apply ep.injective
    rw [ep.apply_symm_apply, hperiod, ep.apply_symm_apply]
  change ep.symm (b2bpol_musical _ R (em (b2_cplxMap J x))) =
    -A.baseChange ℂ (ep.symm (b2bpol_musical _ R (em x)))
  rw [hmark, b60b_musical_skew R K hRskew, map_neg, hep]

theorem b64d_model_homologyCohomology_conj_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (x : ℂ ⊗[ℤ] Λ) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
    letI := b5_smooth Λ F hF Q hQ
    letI := b5_projective Λ F hF Q hQ
    b64d_model_homologyCohomology Λ F hF Q hQ (b2_conj Λ x) =
      HodgeBlocks.sigmaQ _ (b64d_model_homologyCohomology Λ F hF Q hQ x) := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  let X := b5_model Λ F hF Q
  let e := b5_periodEquiv Λ F hF Q hQ
  let R := b4b_transportForm Λ X e Q
  let em := LinearEquiv.baseChange ℤ ℂ _ _ e.toIntLinearEquiv
  let ep := LinearEquiv.baseChange ℚ ℂ _ _ (b60b_periodLinearEquiv X)
  have hep (z : ℂ ⊗[ℚ] HQ X 1) :
      ep (HodgeBlocks.sigmaQ _ z) = HodgeBlocks.sigmaQ _ (ep z) :=
    HodgeBlocks.QHodgeStructure.complexificationCongr_sigmaQR
      (V := HQ X 1) (W := b2b_dual (b2_abelianLattice X))
      (b60b_periodLinearEquiv X) z
  change ep.symm (b2bpol_musical _ R (em (b2_conj Λ x))) =
    HodgeBlocks.sigmaQ _ (ep.symm (b2bpol_musical _ R (em x)))
  apply ep.injective
  rw [ep.apply_symm_apply, hep, ep.apply_symm_apply, b2bpol_sigma_musical]
  congr 1
  exact (b2a_conj_cplxMap e.toAddMonoidHom x).symm

theorem b64d_model_homologyCohomology_pairing_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (x y : ℂ ⊗[ℤ] Λ) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
    letI := b5_smooth Λ F hF Q hQ
    letI := b5_projective Λ F hF Q hQ
    b2_abelianPairing (b5_model Λ F hF Q) (b64d_model_homologyCohomology Λ F hF Q hQ x)
      (b2_cplxMap (b5_periodEquiv Λ F hF Q hQ).toAddMonoidHom y) =
      Q.baseChange ℂ x y := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  let X := b5_model Λ F hF Q
  let e := b5_periodEquiv Λ F hF Q hQ
  let R := b4b_transportForm Λ X e Q
  let em := LinearEquiv.baseChange ℤ ℂ _ _ e.toIntLinearEquiv
  let ep := LinearEquiv.baseChange ℚ ℂ _ _ (b60b_periodLinearEquiv X)
  have hpair (u : ℂ ⊗[ℚ] HQ X 1) (v : ℂ ⊗[ℤ] b2_abelianLattice X) :
      b2_abelianPairing X u v = b2b_pairing _ (ep u) v := by
    induction u using TensorProduct.inductionOn with
    | add u w hu hw => simp only [map_add, LinearMap.add_apply, hu, hw]
    | tmul c u =>
      induction v using TensorProduct.inductionOn with
      | add v w hv hw => simp only [map_add, hv, hw]
      | tmul d v => rfl
  change b2_abelianPairing X (ep.symm (b2bpol_musical _ R (em x))) (em y) = _
  rw [hpair, ep.apply_symm_apply, b2bpol_pairing_musical]
  induction x using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add, LinearMap.add_apply, hu, hv]
  | tmul c u =>
    induction y using TensorProduct.inductionOn with
    | add v w hv hw => simp only [map_add, hv, hw]
    | tmul d v =>
      rw [LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul,
        LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul]
      change Q (e.symm (e u)) (e.symm (e v)) • (c * d) = Q u v • (c * d)
      rw [e.symm_apply_apply, e.symm_apply_apply]

attribute [local irreducible] b5_model

set_option maxHeartbeats 400000 in
theorem b64d_model_homologyCohomology_specializes_aux (τ : g32m_Domain) :
    HEq (b64d_model_homologyCohomology b60_Lattice (b60_F τ) (b60_weight_one τ)
      b60_E ((b60_riemann_iff τ).2 τ.property)) (b60b_homologyCohomologyEquiv τ) := by
  unfold b64d_model_homologyCohomology b60b_homologyCohomologyEquiv
  dsimp only [b60b_model, b60b_marking, b60b_form, b60b_grp]
  rfl

end HodgeLean.Foundations.Program
