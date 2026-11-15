import HodgeLean.Foundations.Program.PeriodFibreMarkingDefs
import HodgeLean.Foundations.Program.PeriodFibreMarkingLinear

/-! # Rational comparison and retained fibre marking
Implication from integral Riemann data and a rational marking to fibre comparisons.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry Set Manifold HodgeLean.Papers
open HodgeLean.RealDefs HodgeLean.Adapters
open scoped TensorProduct ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

theorem b64e_model_rational_complexification_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (c : ℂ) (l : Λ) :
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  (b64e_model_rational Λ F hF Q hQ).toLinearMap.baseChange ℂ
    (c ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] l)) =
      b64d_model_homologyCohomology Λ F hF Q hQ (c ⊗ₜ[ℤ] l) := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  rw [LinearMap.baseChange_tmul]
  change c ⊗ₜ[ℚ] _ =
    (LinearEquiv.baseChange ℚ ℂ _ _ (b60b_periodLinearEquiv _)).symm
      (b2bpol_musical _ _
        ((LinearEquiv.baseChange ℤ ℂ _ _ (b5_periodEquiv Λ F hF Q hQ).toIntLinearEquiv)
          (c ⊗ₜ[ℤ] l)))
  rw [LinearEquiv.baseChange_tmul, b2bpol_musical_tmul]
  rfl

theorem b64e_model_rational_extension (Λ : Type) [AddCommGroup Λ]
    [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    LinearEquiv.baseChange ℚ ℂ _ _ (b64e_model_rational Λ F hF Q hQ) =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ Λ).trans
        (b64d_model_homologyCohomology Λ F hF Q hQ) := by
  apply LinearEquiv.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c y =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
    | tmul q l =>
      change c ⊗ₜ[ℚ] ((b64e_model_rational Λ F hF Q hQ) (q ⊗ₜ[ℤ] l)) =
        b64d_model_homologyCohomology Λ F hF Q hQ ((q • c) ⊗ₜ[ℤ] l)
      rw [show q ⊗ₜ[ℤ] l = q • ((1 : ℚ) ⊗ₜ[ℤ] l) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul,
        TensorProduct.tmul_smul, ← TensorProduct.smul_tmul']
      exact b64e_model_rational_complexification_aux Λ F hF Q hQ (q • c) l

attribute [local irreducible] b5_model

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem b64e_fibre_marking_complexification_aux (R : rf8_SharedFamily)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (t : b6t_polydisc mr_base) (hm : b64i_period R b63gP_s₀ m t.val ∈ g32m_Domain) (x : ℂ ⊗[ℤ] b60_Lattice) :
  (b64e_fibre_marking R m t hm).toLinearMap.baseChange ℂ
    (b60b_homologyCohomologyEquiv ⟨b64i_period R b63gP_s₀ m t.val, hm⟩ x) =
    b64e_retained_complex R t ((b64b_complexMarking _ m).symm x) := by
  letI := Module.Free.of_basis (b63gR_basis R)
  letI := Module.Finite.of_basis (b63gR_basis R)
  let τ : g32m_Domain := ⟨b64i_period R b63gP_s₀ m t.val, hm⟩
  have hu := b64e_model_rational_extension b60_Lattice _ (b60_weight_one τ)
    b60_E ((b60_riemann_iff τ).2 hm)
  rw [eq_of_heq (b64d_model_homologyCohomology_specializes τ)] at hu
  have hr : LinearEquiv.baseChange ℚ ℂ _ _ (b64e_retained_rational R t) =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ _).trans
        (b64e_retained_complex R t) :=
    b64e_model_rational_extension _ _ _ _ _
  change (LinearEquiv.baseChange ℚ ℂ _ _
    ((b64e_model_rational b60_Lattice _ (b60_weight_one τ) b60_E
      ((b60_riemann_iff τ).2 hm)).symm.trans
        (m.symm.trans (b64e_retained_rational R t))))
          (b60b_homologyCohomologyEquiv τ x) = _
  rw [LinearEquiv.baseChange_trans, LinearEquiv.baseChange_trans,
    LinearEquiv.baseChange_symm, hu, hr]
  exact congrArg (fun z => b64e_retained_complex R t
    (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ _
      (LinearEquiv.baseChange ℚ ℂ _ _ m.symm
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ b60_Lattice).symm z))))
    ((b60b_homologyCohomologyEquiv τ).symm_apply_apply x)

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem b64e_fibre_marking_action_aux (R : rf8_SharedFamily)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpair : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (R.P b63gP_s₀) (R.Q b63gP_s₀)).baseChange ℚ x y)
    (t : b6t_polydisc mr_base) (hm : b64i_period R b63gP_s₀ m t.val ∈ g32m_Domain) :
  ∀ x, (b64e_fibre_marking R m t hm) ((b60b_univ ⟨b64i_period R b63gP_s₀ m t.val, hm⟩).W.J x) = ((b63gR_family R).fiber t).W.J ((b64e_fibre_marking R m t hm) x) := by
  letI := Module.Free.of_basis (b63gR_basis R)
  letI := Module.Finite.of_basis (b63gR_basis R)
  let τ : g32m_Domain := ⟨b64i_period R b63gP_s₀ m t.val, hm⟩
  let P := (b63gR_family R).fiber t
  let A := b63g2_operator mr_base R.C R.hC (b6t_polydisc mr_base)
    (Subset.refl _) b63gP_s₀
  have hA : R.A b63gP_s₀ = A := by
    apply LinearMap.ext
    intro l
    apply Subtype.val_injective
    exact (R.hA _ l).trans (b63g2_operator_val _ _ _ _ _ _ l).symm
  let u := b60b_homologyCohomologyEquiv τ
  let r := b64e_retained_complex R t
  let c := b64b_complexMarking _ m
  let e := (b64e_fibre_marking R m t hm).toLinearMap.baseChange ℂ
  let ju := (b60b_univ τ).W.J.baseChange ℂ
  let jr := P.W.J.baseChange ℂ
  have he (z) : e (u z) = r (c.symm z) :=
    b64e_fibre_marking_complexification_aux R m t hm z
  have hu (z) : ju (u z) = -u (b60_omegaC z) := by
    rw [b60b_homologyCohomology_intertwines, neg_neg]
    rfl
  have hr (z) : r (A.baseChange ℂ z) = -jr (r z) := by
    exact b64d_model_homologyCohomology_intertwines _ _ _ _ _ A.toAddMonoidHom
      (b63g2_operator_skew mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (R.hG _) (R.P _) (R.hP _) (R.Q _) (R.hQ _)) z
  have hc (z) : c.symm (b60_omegaC z) = A.baseChange ℂ (c.symm z) := by
    apply c.injective
    rw [c.apply_symm_apply]
    have h := b64b_complex_intertwines _ A m (by simpa only [hA] using hJ) (c.symm z)
    exact (h.trans (congrArg b60_omegaC (c.apply_symm_apply z))).symm
  intro x
  apply Module.Flat.tensorProduct_mk_injective ℚ (HQ P.X 1) ℂ
  change e (ju ((1 : ℂ) ⊗ₜ[ℚ] x)) = jr (e ((1 : ℂ) ⊗ₜ[ℚ] x))
  obtain ⟨z, hz⟩ := u.surjective ((1 : ℂ) ⊗ₜ[ℚ] x)
  rw [← hz, hu, map_neg, he, hc, hr, neg_neg, he]


set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem b64e_fibre_marking_filtration_aux (R : rf8_SharedFamily)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpair : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (R.P b63gP_s₀) (R.Q b63gP_s₀)).baseChange ℚ x y)
    (t : b6t_polydisc mr_base) (hm : b64i_period R b63gP_s₀ m t.val ∈ g32m_Domain) :
  (b60c_F (b60b_univ ⟨b64i_period R b63gP_s₀ m t.val, hm⟩)).map ((b64e_fibre_marking R m t hm).toLinearMap.baseChange ℂ) = b60c_F ((b63gR_family R).fiber t) := by
  letI := Module.Free.of_basis (b63gR_basis R)
  letI := Module.Finite.of_basis (b63gR_basis R)
  let τ : g32m_Domain := ⟨b64i_period R b63gP_s₀ m t.val, hm⟩
  let G := b63e_transportedF mr_base R.C R.hC (b6t_polydisc mr_base)
    (Subset.refl _) R.P b63gP_s₀ t
  let u := b60b_homologyCohomologyEquiv τ
  let r := b64e_retained_complex R t
  let c := b64b_complexMarking _ m
  let e := (b64e_fibre_marking R m t hm).toLinearMap.baseChange ℂ
  have hu : (b60_F τ).map u.toLinearMap = b60c_F (b60b_univ τ) :=
    b60b_homologyCohomology_F τ
  have hr : G.map r.toLinearMap = b60c_F ((b63gR_family R).fiber t) :=
    b64d_model_homologyCohomology_F _ _ _ _ _
  have hc : b60_F τ = G.map c.toLinearMap := by
    have h := (b64i_chart R b63gP_s₀ m hJ hpair t.val t.property).2
    simpa only [b64c_markedF, rf8_transportedFamily, dite_eq_left t.property] using h
  have he : e.comp u.toLinearMap = r.toLinearMap.comp c.symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    exact b64e_fibre_marking_complexification_aux R m t hm x
  change (b60c_F (b60b_univ τ)).map e = _
  apply Eq.trans ?_ hr
  rw [← hu, ← Submodule.map_comp, he, hc]
  rw [Submodule.map_comp]
  have hid : c.symm.toLinearMap.comp c.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    exact c.symm_apply_apply
  have hcancel : (G.map c.toLinearMap).map c.symm.toLinearMap = G := by
    rw [← Submodule.map_comp, hid, Submodule.map_id]
  exact congrArg (Submodule.map r.toLinearMap) hcancel

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2000 in
theorem b64e_fibre_marking_polarization_aux (R : rf8_SharedFamily)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpair : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (R.P b63gP_s₀) (R.Q b63gP_s₀)).baseChange ℚ x y)
    (t : b6t_polydisc mr_base) (hm : b64i_period R b63gP_s₀ m t.val ∈ g32m_Domain) :
  exteriorPower.map 2 (b64e_fibre_marking R m t hm).toLinearMap
    (polarizationVec (torusCohomology_cupProductOf (b60b_univ ⟨b64i_period R b63gP_s₀ m t.val, hm⟩).X) (b60b_univ ⟨b64i_period R b63gP_s₀ m t.val, hm⟩).pol) =
      polarizationVec (torusCohomology_cupProductOf ((b63gR_family R).fiber t).X) ((b63gR_family R).fiber t).pol := by
  letI := Module.Free.of_basis (b63gR_basis R)
  letI := Module.Finite.of_basis (b63gR_basis R)
  let τ : g32m_Domain := ⟨b64i_period R b63gP_s₀ m t.val, hm⟩
  let P := (b63gR_family R).fiber t
  let eu := b64e_model_rational b60_Lattice _ (b60_weight_one τ)
    b60_E ((b60_riemann_iff τ).2 hm)
  let er := b64e_retained_rational R t
  let e := b64e_fibre_marking R m t hm
  letI := (torusCohomology_cupProductOf (b60b_univ τ).X).finite
  letI := (torusCohomology_cupProductOf P.X).finite
  let nu := (b60b_member τ).nondegenerate
  let nr := (b63gR_family R).nondegenerate t
  apply b60c_bivector_map_of_dualForm e nu nr
  intro x y
  obtain ⟨a, rfl⟩ := eu.surjective x
  obtain ⟨b, rfl⟩ := eu.surjective y
  have he (z) : e (eu z) = er (m.symm z) := by
    change er (m.symm (eu.symm (eu z))) = _
    rw [eu.symm_apply_apply]
  have hu (v w) : HodgeLean.Foundations.Symplectic.dualForm nu (eu v) (eu w) =
      b60_E.baseChange ℚ v w := by
    let q := b63g_modelForm b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E
      ((b60_riemann_iff τ).2 hm)
    let n := b2_abelian_nondegenerate (b60b_model τ) q
      (b63g_modelForm_riemann b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E
        ((b60_riemann_iff τ).2 hm))
    have hforms : b60b_form τ = q := by
      ext l k
      rfl
    have hv : polarizationVec (torusCohomology_cupProductOf (b60b_model τ)) (b60b_pol τ) =
        polarizationVec (torusCohomology_cupProductOf (b60b_model τ))
          (latticeClassHQ (b60b_model τ) (b2_bilinToAddHom q)) := by
      exact congrArg (fun B => polarizationVec (torusCohomology_cupProductOf (b60b_model τ))
        (latticeClassHQ (b60b_model τ) (b2_bilinToAddHom B))) hforms
    have hn := b60b_dualForm_congr hv nu n
    have h := b64e_model_rational_form b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E
      ((b60_riemann_iff τ).2 hm) v w
    exact (congrArg (fun B : LinearMap.BilinForm ℚ (HQ (b60b_model τ) 1) => B (eu v) (eu w)) hn).trans h
  have hr (v w) : HodgeLean.Foundations.Symplectic.dualForm nr (er v) (er w) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (R.P b63gP_s₀) (R.Q b63gP_s₀)).baseChange ℚ v w := by
    let L := b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀
    let F := b63e_transportedF mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) R.P b63gP_s₀ t
    let Q := b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
      b63gP_s₀ (R.P b63gP_s₀) (R.Q b63gP_s₀)
    have hW := b63e_weight_one_riemann mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) R.hG mr_base_mem_chart R.atlas.f R.atlas.hf R.atlas.hsurj R.hk
      R.Q₀ R.hQ₀ R.Q R.hQ R.P R.hP b63gP_s₀ t
    let q := b63g_modelForm L F hW.1 Q hW.2
    let n := b2_abelian_nondegenerate P.X q (b63g_modelForm_riemann L F hW.1 Q hW.2)
    have hv : polarizationVec (torusCohomology_cupProductOf P.X) P.pol =
        polarizationVec (torusCohomology_cupProductOf P.X)
          (latticeClassHQ P.X (b2_bilinToAddHom q)) := by
      have hclass : P.pol = latticeClassHQ P.X (b2_bilinToAddHom q) := by
        dsimp only [P, b63gR_family, b63g5_fiber, b63g2_sixfold]
        rfl
      exact congrArg (polarizationVec (torusCohomology_cupProductOf P.X)) hclass
    have hn := b60b_dualForm_congr hv nr n
    have h := b64e_model_rational_form L F hW.1 Q hW.2 v w
    exact (congrArg (fun B : LinearMap.BilinForm ℚ (HQ P.X 1) => B (er v) (er w)) hn).trans h
  rw [he, he, hr, hu]
  have h := hpair (m.symm a) (m.symm b)
  rw [m.apply_symm_apply, m.apply_symm_apply] at h
  exact h.symm


set_option maxHeartbeats 400000 in
set_option maxRecDepth 2000 in
theorem b64e_kIsog_aux (R : rf8_SharedFamily)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpair : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (R.P b63gP_s₀) (R.Q b63gP_s₀)).baseChange ℚ x y)
    (t : b6t_polydisc mr_base) (hm : b64i_period R b63gP_s₀ m t.val ∈ g32m_Domain) :
  g32t_KIsog ((b63gR_family R).fiber t) (b60b_univ ⟨b64i_period R b63gP_s₀ m t.val, hm⟩) := by
  obtain ⟨N, hN, f, hf, hi, _, hfJ, hfpol⟩ :=
    b60c_uniformization ((b63gR_family R).fiber t)
      ⟨b64i_period R b63gP_s₀ m t.val, hm⟩ (b64e_fibre_marking R m t hm)
      (b64e_fibre_marking_action_aux R m hJ hpair t hm)
      (b64e_fibre_marking_filtration_aux R m hJ hpair t hm)
      (b64e_fibre_marking_polarization_aux R m hJ hpair t hm)
  refine ⟨f, hf, hi, hfJ, (N : ℚ) ^ 2, ?_, hfpol⟩
  exact pow_pos (Nat.cast_pos.mpr hN) 2


theorem b64e_hisog_aux (R : rf8_SharedFamily)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpair : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (R.P b63gP_s₀) (R.Q b63gP_s₀)).baseChange ℚ x y)
    (Fm : g32m_UniversalFamily) (hFm : Fm.univ = b60b_univ) :
  ∀ (t : b6t_polydisc mr_base)
    (hm : b64i_period R b63gP_s₀ m t.val ∈ g32m_Domain),
    g32t_KIsog ((b63gR_family R).fiber t) (Fm.univ ⟨b64i_period R b63gP_s₀ m t.val, hm⟩) := by
  intro t hm
  rw [hFm]
  exact b64e_kIsog_aux R m hJ hpair t hm


end HodgeLean.Foundations.Program
