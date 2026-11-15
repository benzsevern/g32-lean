import HodgeLean.Foundations.Program.G32SelectedRealizationJacobianPeriod
import HodgeLean.Foundations.Program.G32SelectedRealizationReferenceProjection
import HodgeLean.Foundations.Program.G32SelectedRealizationMarkedGroupRing
import HodgeLean.Foundations.Program.G32SelectedRealizationMarkedPeriod
import HodgeLean.Foundations.Program.G32SelectedRealizationProjector
import HodgeLean.Foundations.Program.G32SelectedRealizationImageModel
import HodgeLean.Foundations.Program.G32SelectedRealizationIntegralProjector
import HodgeLean.Foundations.Program.G32SelectedRealizationUniformSignatures
import HodgeLean.Foundations.Program.G32SelectedRealizationHodgeRange
import HodgeLean.Foundations.Program.G32SelectedRealizationComapConjugation
import HodgeLean.Foundations.Program.G32SelectedRealizationBalancedRank
import HodgeLean.Foundations.Program.G32SelectedRealizationPositive

noncomputable section
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
open scoped TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

theorem g32y_scalar_trans {U V : Type*} [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V] {m h : ℕ}
    (r : U ≃ₗ[ℚ] V) (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (a : cyc_Field m) :
    r.toLinearMap ∘ₗ cyc_scalar (r.trans e) a = cyc_scalar e a ∘ₗ r.toLinearMap := by
  ext x
  exact r.apply_symm_apply _

theorem g32y_eigenspace_trans {U V : Type*} [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V] {m h : ℕ}
    (r : U ≃ₗ[ℚ] V) (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m))
    (σ : cyc_Field m →ₐ[ℚ] ℂ) :
    cyc_eigenspace (r.trans e) σ =
      (cyc_eigenspace e σ).comap (r.baseChange ℚ ℂ _ _).toLinearMap := by
  have hc (a : cyc_Field m) :
      (r.baseChange ℚ ℂ _ _).toLinearMap ∘ₗ (cyc_scalar (r.trans e) a).baseChange ℂ =
        (cyc_scalar e a).baseChange ℂ ∘ₗ (r.baseChange ℚ ℂ _ _).toLinearMap := by
    simpa only [LinearMap.baseChange_comp, LinearEquiv.coe_baseChange] using
      congrArg (LinearMap.baseChange ℂ) (g32y_scalar_trans r e a)
  ext x
  simp only [cyc_eigenspace, Submodule.mem_iInf, Submodule.mem_comap,
    Module.End.mem_eigenspace_iff]
  constructor
  · intro hx a
    have hh := LinearMap.congr_fun (hc a) x
    change (r.baseChange ℚ ℂ _ _) ((cyc_scalar (r.trans e) a).baseChange ℂ x) = _ at hh
    rw [hx a, map_smul] at hh
    exact hh.symm
  · intro hx a
    apply (r.baseChange ℚ ℂ _ _).injective
    rw [map_smul]
    exact (LinearMap.congr_fun (hc a) x).trans (hx a)

section
attribute [local irreducible] b63l_saturation b5_model b2_abelianF b5_periodEquiv

set_option maxHeartbeats 400000 in
theorem g32y_marked_comparison_aux {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c)))
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a) :
    ∃ i : (b65z_fiber D B t).X ⟶ g32x_J D t,
    ∃ q : g32x_J D t ⟶ (b65z_fiber D B t).X,
    ∃ N : ℕ, 0 < N ∧ IsMonHom i ∧ IsMonHom q ∧
      i ≫ q = 𝟙 (b65z_fiber D B t).X ^ N ∧
      (∃ z : g32p_G → ℤ, q ≫ i = ∏ a, (f a).hom ^ z a) ∧
      LinearMap.range (homPullback q 1) = LinearMap.range (g32x_projector D t) ∧
      ∃ a : g32p_G, (∃ l : ℂ, l ^ 2 + l + 1 = 0 ∧ b4b_toMatrix a = l • 1) ∧
        ∀ x, homPullback q 1 ((b65z_fiber D B t).W.J x) =
          homPullback q 1 x + (2 : ℚ) • homPullback (f a).hom 1 (homPullback q 1 x) := by
  classical
  let FA := b63e_transportedF c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _)
    D.P (b65z_s₀ c) t
  obtain ⟨eA, heA, heAop⟩ := g32y_marked_period_equivalence D t B
  obtain ⟨eJ, heJ, heJop⟩ := g32y_jacobian_period_equivalence D t
  let i0 := b63e_transportMap c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _)
    D.P (b65z_s₀ c) t
  obtain ⟨p0, hIp, hpI, hpF⟩ := g32y_reference_projection D t
  let iL := eJ.toAddMonoidHom.comp (i0.toAddMonoidHom.comp eA.symm.toAddMonoidHom)
  let pL := eA.toAddMonoidHom.comp (p0.toAddMonoidHom.comp eJ.symm.toAddMonoidHom)
  have hiF : FA ≤ (b3_periodF ℂ (b65z_fibre c D.C t)).comap (b2_cplxMap i0.toAddMonoidHom) :=
    le_refl _
  have hiL := g32y_transport_lattice_map_preserves eA eJ _ _ _ _ heA heJ
    i0.toAddMonoidHom hiF
  have hpL := g32y_transport_lattice_map_preserves eJ eA _ _ _ _ heJ heA
    p0.toAddMonoidHom hpF
  have hret : pL.comp iL = 116640 • AddMonoidHom.id _ := by
    apply AddMonoidHom.ext
    intro l
    rw [AddMonoidHom.comp_apply, AddMonoidHom.smul_apply, AddMonoidHom.id_apply]
    change eA (p0 (eJ.symm (eJ (i0 (eA.symm l))))) = 116640 • l
    rw [eJ.symm_apply_apply]
    have hh := LinearMap.congr_fun hpI (eA.symm l)
    change p0 (i0 (eA.symm l)) = (116640 : ℤ) • eA.symm l at hh
    rw [hh]
    have hm := map_zsmul eA.toAddMonoidHom (116640 : ℤ) (eA.symm l)
    simp only [AddEquiv.coe_toAddMonoidHom] at hm
    rw [hm, eA.apply_symm_apply]
    exact natCast_zsmul _ _
  let b : AbelianEnd (g32x_J D t) := ∑ a, b4b_projectorCoeff a • f a
  have hb : homPullback b.hom 1 = g32x_projector D t := by
    rw [show b.hom = ∏ a, (f a).hom ^ b4b_projectorCoeff a from
      g32y_abelianEnd_sum_hom _ f b4b_projectorCoeff]
    exact g32y_retained_groupRing_action D t f hf
  have hφ : ∀ x l, abelianPeriod (g32x_J D t) (abelianEndAction _ b x) l =
      abelianPeriod (g32x_J D t) x (iL (pL l)) := by
    intro x l
    obtain ⟨v, rfl⟩ := eJ.surjective l
    change abelianPeriod _ (homPullback b.hom 1 x) (eJ v) = _
    rw [hb]
    have heL : eJ ((b4_groupEnd ℂ b4b_projectorCoeff) v) = iL (pL (eJ v)) := by
      change eJ ((b4_groupEnd ℂ b4b_projectorCoeff) v) =
        eJ (i0 (eA.symm (eA (p0 (eJ.symm (eJ v))))))
      rw [eJ.symm_apply_apply, eA.symm_apply_apply]
      exact congrArg eJ (LinearMap.congr_fun hIp v).symm
    exact (heJop (b4_groupEnd ℂ b4b_projectorCoeff) x v).trans
      (congrArg (abelianPeriod (g32x_J D t) x) heL)
  obtain ⟨i, q, hi, hq, hr, hqi, hip, hqp⟩ :=
    g32y_lattice_retract_periods (g32x_J D t) (b65z_fiber D B t).X b iL pL hiL hpL
      116640 hret hφ
  refine ⟨i, q, 116640, by norm_num, hi, hq, hr,
    ⟨b4b_projectorCoeff, hqi.trans (g32y_abelianEnd_sum_hom _ f _)⟩, ?_,
    b63d_scalarElement⁻¹, g32y_inverse_centre_scalar, ?_⟩
  · have hc : homPullback i 1 ∘ₗ homPullback q 1 = (116640 : ℚ) • LinearMap.id := by
      rw [← spec_homPullback_comp, hr, ← zpow_natCast, spec_homPullback_zpow,
        spec_homPullback_id]
      simp
    have hs : Function.Surjective (homPullback i 1) := by
      intro x
      refine ⟨(116640 : ℚ)⁻¹ • homPullback q 1 x, ?_⟩
      rw [map_smul, ← LinearMap.comp_apply, hc, LinearMap.smul_apply,
        LinearMap.id_apply, smul_smul]
      norm_num
    rw [← hb, ← hqi, spec_homPullback_comp,
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hs)]
  · let Z := eJ.toAddMonoidHom.comp
        ((b4_latticeAct ℂ (C := b65z_fibre c D.C t) b63d_scalarElement).comp
          eJ.symm.toAddMonoidHom)
    let A := eA.toAddMonoidHom.comp
      ((b63g2_operator c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _)
        (b65z_s₀ c)).toAddMonoidHom.comp eA.symm.toAddMonoidHom)
    apply g32y_weil_of_period_intertwining _ _ q (f b63d_scalarElement⁻¹).hom
      pL Z _ A hqp
    · intro x l
      obtain ⟨v, rfl⟩ := eJ.surjective l
      rw [hf]
      change abelianPeriod _ (g32x_operator D t (b4_latticeAct ℂ
        (b63d_scalarElement⁻¹)⁻¹) x) (eJ v) =
          abelianPeriod _ x (eJ (b4_latticeAct ℂ b63d_scalarElement (eJ.symm (eJ v))))
      rw [inv_inv, eJ.symm_apply_apply]
      exact heJop _ x v
    · intro x l
      obtain ⟨v, rfl⟩ := eA.surjective l
      change abelianPeriod _ ((b65z_fiber D B t).W.J x) (eA v) =
        abelianPeriod _ x (eA ((b63g2_operator c D.C D.hC (b6t_polydisc c)
          (Set.Subset.refl _) (b65z_s₀ c)) (eA.symm (eA v))))
      rw [eA.symm_apply_apply]
      exact heAop x v
    · intro l
      change eA ((b63g2_operator c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _)
        (b65z_s₀ c)) (eA.symm (eA (p0 (eJ.symm l))))) =
          eA (p0 (eJ.symm l)) + 2 • eA (p0 (eJ.symm
            (eJ (b4_latticeAct ℂ b63d_scalarElement (eJ.symm l)))))
      rw [eA.symm_apply_apply, eJ.symm_apply_apply,
        g32y_reference_projection_weil D t p0 hIp]
      simp only [two_zsmul, two_nsmul]
      let x := p0 (eJ.symm l)
      let y := p0 (b4_latticeAct ℂ b63d_scalarElement (eJ.symm l))
      change eA (x + (y + y)) = eA x + (eA y + eA y)
      exact (eA.map_add' x (y + y)).trans
        (congrArg (fun z ↦ eA x + z) (eA.map_add' y y))


end

theorem g32y_primitive_projector_aux {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a)
    (S : g32p_Supplier) :
    letI : Fintype S.H := Fintype.ofFinite S.H
    ∃ u : S.H → ℚ,
      let e : Module.End ℚ (HQ (g32x_J D t) 1) :=
        ∑ h : S.H, u h • homPullback (f h).hom 1
      e ∘ₗ e = e ∧ LinearMap.range e = g32p_primitive (fun a ↦ (f a).hom) S := by
  classical
  letI : Fintype S.H := Fintype.ofFinite S.H
  obtain ⟨h1, hmul⟩ := g32x_deck_laws D t f hf
  let R : Representation ℚ S.H (HQ (g32x_J D t) 1) := {
    toFun := fun h ↦ homPullback (f h).hom 1
    map_one' := by
      change homPullback (f 1).hom 1 = 1
      rw [h1, spec_homPullback_id]
      rfl
    map_mul' := by
      intro a b
      change homPullback (f ((a : g32p_G) * (b : g32p_G))).hom 1 = _
      rw [hmul, spec_homPullback_comp]
      rfl }
  exact g32y_relation_projector R {h | S.χ h = 1}
    {h | S.χ h = Multiplicative.ofAdd 1} (Polynomial.cyclotomic S.m ℚ)

set_option maxHeartbeats 400000 in
theorem g32y_primitive_image_aux {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a)
    (S : g32p_Supplier)
    (hS : g32p_Admissible (fun a ↦ (f a).hom) S) :
    ∃ (P : Over (Spec ↧ℂ)) (_ : GrpObj P) (_ : IsCommMonObj P)
      (_ : IsIntegral P.left) (_ : Smooth P.hom) (_ : IsProjective P.hom),
    ∃ i : P ⟶ g32x_J D t, ∃ q : g32x_J D t ⟶ P,
    ∃ N : ℕ, 0 < N ∧ IsMonHom i ∧ IsMonHom q ∧
      i ≫ q = 𝟙 P ^ N ∧
      LinearMap.range (homPullback q 1) = g32p_primitive (fun a ↦ (f a).hom) S := by
  classical
  letI : Fintype S.H := Fintype.ofFinite S.H
  obtain ⟨u, hu, hR⟩ := g32y_primitive_projector_aux D t f hf S
  obtain ⟨N, hN, b, hb, hbb⟩ :=
    g32y_integral_projector (g32x_J D t) (fun h : S.H ↦ f h) u hu
  obtain ⟨φ, hφ⟩ := spec_abelianEndAction_period (g32x_J D t) b
  have hsq := g32y_lattice_scaled_idempotent (g32x_J D t) b φ hφ N hbb
  let F := b3_periodF ℂ (b65z_fibre c D.C t)
  let hF : b2_IsWeightOne (g32x_L D t) F := b3_isWeightOne (by simp)
  let hQ : b2_IsRiemannForm (g32x_L D t) F (D.Q t) :=
    b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t)
  let Q := b63g_modelForm (g32x_L D t) F hF (D.Q t) hQ
  have hmodelQ := b63g_modelForm_riemann (g32x_L D t) F hF (D.Q t) hQ
  obtain ⟨P, gP, cP, iP, sP, pP, i, q, hi, hq, hr, hqR⟩ :=
    g32y_abelian_image (g32x_J D t) Q hmodelQ b φ hφ N hN hsq
  let := gP
  let := cP
  let := iP
  let := sP
  let := pP
  refine ⟨P, gP, cP, iP, sP, pP, i, q, N, hN, hi, hq, hr, ?_⟩
  rw [hqR]
  change LinearMap.range (abelianEndAction (g32x_J D t) b) = _
  rw [hb, LinearMap.range_smul _ _ (by exact_mod_cast hN.ne')]
  exact hR

theorem g32y_primitive_balance_aux {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a)
    (S : g32p_Supplier)
    (hS : g32p_Admissible (fun a ↦ (f a).hom) S) :
    let V := g32p_primitive (fun a ↦ (f a).hom) S
    let M := (abelianVarietyCohomologyOf (finiteBetti_abelian (g32x_J D t))
      (spec_bettiDeRhamIso_abelian (g32x_J D t))
      (hodgeDecomposition_of_abelian (g32x_J D t))
      (torusCohomology_cupProductOf (g32x_J D t))).weight1
    ∃ k : ℕ, 0 < k ∧ ∃ e : V ≃ₗ[ℚ] (Fin (2 * k) → cyc_Field S.m),
      (∀ h : S.H, V.subtype ∘ₗ cyc_scalar e (g32p_fieldValue S h) =
        homPullback (f h).hom 1 ∘ₗ V.subtype) ∧
      (∀ a pq, ((M.H pq).comap (V.subtype.baseChange ℂ)).map
        ((cyc_scalar e a).baseChange ℂ) ≤ (M.H pq).comap (V.subtype.baseChange ℂ)) ∧
      ∀ σ : cyc_Field S.m →ₐ[ℚ] ℂ,
        Module.finrank ℂ ↥(cyc_eigenspace e σ ⊓
          (M.H (1, 0)).comap (V.subtype.baseChange ℂ)) = k := by
  classical
  let V := g32p_primitive (fun a ↦ (f a).hom) S
  let M := (abelianVarietyCohomologyOf (finiteBetti_abelian (g32x_J D t))
    (spec_bettiDeRhamIso_abelian (g32x_J D t))
    (hodgeDecomposition_of_abelian (g32x_J D t))
    (torusCohomology_cupProductOf (g32x_J D t))).weight1
  obtain ⟨d, e, he, hp⟩ := g32y_primitive_hodge_coordinates D t f hf S
  have hd : 0 < d := g32y_coordinate_rank_positive V hS.2 e
  obtain ⟨k, hs⟩ : ∃ k : ℕ, ∀ σ : cyc_Field S.m →ₐ[ℚ] ℂ,
      Module.finrank ℂ ↥(cyc_eigenspace e σ ⊓
        (M.H (1, 0)).comap (V.subtype.baseChange ℂ)) = k := by
    refine ⟨Module.finrank ℂ ↥(cyc_eigenspace e (g32p_complexEmbedding S) ⊓
      (M.H (1, 0)).comap (V.subtype.baseChange ℂ)), fun σ ↦ ?_⟩
    exact g32y_primitive_signatures_equal D t hg f hf S hS e he σ (g32p_complexEmbedding S)
  letI : Fintype S.H := Fintype.ofFinite S.H
  obtain ⟨u, hu, hR⟩ := g32y_primitive_projector_aux D t f hf S
  have hcompl := g32y_abelian_range_hodge_complement (g32x_J D t)
    (fun h : S.H ↦ f h) u V hR
  have hswap := g32y_rational_comap_conjugation V.subtype (M.H (1, 0))
    (M.H (0, 1)) (M.conj_symm 1 0)
  let σ := g32p_complexEmbedding S
  let τ : cyc_Field S.m →ₐ[ℚ] ℂ :=
    { toFun := fun a ↦ star (σ a)
      map_zero' := by simp
      map_one' := by simp
      map_add' := by intros; simp
      map_mul' := by intros; simp
      commutes' := by intro r; rw [σ.commutes]; simp }
  have hdim : d = 2 * k := g32y_cyclotomic_balanced_rank S.three_le hd e
    ((M.H (1, 0)).comap (V.subtype.baseChange ℂ))
    ((M.H (0, 1)).comap (V.subtype.baseChange ℂ))
    hcompl.sup_eq_top hcompl.disjoint hswap
    (fun a i ↦ by cases i <;> exact hp a _) σ τ (fun _ ↦ rfl) hs
  have hk : 0 < k := by omega
  subst d
  exact ⟨k, hk, e, he, hp, hs⟩

theorem g32y_part_aux {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a)
    (S : g32p_Supplier)
    (hS : g32p_Admissible (fun a ↦ (f a).hom) S) :
    Nonempty (g32p_Part (g32x_J D t) (fun a ↦ (f a).hom) S) := by
  classical
  obtain ⟨P, gP, cP, iP, sP, pP, i, q, N, hN, hi, hq, hr, hR⟩ :=
    g32y_primitive_image_aux D t f hf S hS
  let := gP
  let := cP
  let := iP
  let := sP
  let := pP
  let := hi
  let := hq
  let V := g32p_primitive (fun a ↦ (f a).hom) S
  have hn : (N : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hcomp : homPullback i 1 ∘ₗ homPullback q 1 = (N : ℚ) • LinearMap.id := by
    rw [← spec_homPullback_comp, hr, ← zpow_natCast, spec_homPullback_zpow,
      spec_homPullback_id]
    simp only [Int.cast_natCast]
  have hqi : Function.Injective (homPullback q 1) := by
    intro x y h
    have hh := congrArg (homPullback i 1) h
    change (homPullback i 1 ∘ₗ homPullback q 1) x =
      (homPullback i 1 ∘ₗ homPullback q 1) y at hh
    rw [hcomp] at hh
    exact (smul_right_injective _ hn) hh
  let r : HQ P 1 ≃ₗ[ℚ] V :=
    (LinearEquiv.ofInjective (homPullback q 1) hqi).trans (LinearEquiv.ofEq _ _ hR)
  have hsub : V.subtype ∘ₗ r.toLinearMap = homPullback q 1 := rfl
  have hsubC : V.subtype.baseChange ℂ ∘ₗ (r.baseChange ℚ ℂ _ _).toLinearMap =
      (homPullback q 1).baseChange ℂ :=
    (LinearMap.baseChange_comp _ _).symm.trans (congrArg (LinearMap.baseChange ℂ) hsub)
  have hcompC : (homPullback i 1).baseChange ℂ ∘ₗ (homPullback q 1).baseChange ℂ =
      (N : ℚ) • LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hcomp, LinearMap.baseChange_smul, LinearMap.baseChange_id]
  have hH (pq : ℤ × ℤ) :
      ((cohomologyHodgePiece (g32x_J D t) 1 pq).comap (V.subtype.baseChange ℂ)).comap
        (r.baseChange ℚ ℂ _ _).toLinearMap = cohomologyHodgePiece P 1 pq := by
    rw [← Submodule.comap_comp, hsubC]
    apply le_antisymm
    · intro x hx
      have hh := spec_homPullback_hodgePiece_one i pq (Submodule.mem_map_of_mem hx)
      have he := LinearMap.congr_fun hcompC x
      change (homPullback i 1).baseChange ℂ ((homPullback q 1).baseChange ℂ x) =
        (N : ℚ) • x at he
      rw [he] at hh
      exact (Submodule.smul_mem_iff _ hn).mp hh
    · exact (Submodule.map_le_iff_le_comap).mp (spec_homPullback_hodgePiece_one q pq)
  obtain ⟨k, hk, e, he, hp, hs⟩ := g32y_primitive_balance_aux D t hg f hf S hS
  let := (torusCohomology_cupProductOf P).finite
  have hpres (a : cyc_Field S.m) (pq : ℤ × ℤ) :
      (cohomologyHodgePiece P 1 pq).map ((cyc_scalar (r.trans e) a).baseChange ℂ) ≤
        cohomologyHodgePiece P 1 pq := by
    rw [← hH pq]
    rintro _ ⟨x, hx, rfl⟩
    have hh := hp a pq (Submodule.mem_map_of_mem hx)
    have hc : (r.baseChange ℚ ℂ _ _).toLinearMap ∘ₗ
        (cyc_scalar (r.trans e) a).baseChange ℂ =
          (cyc_scalar e a).baseChange ℂ ∘ₗ (r.baseChange ℚ ℂ _ _).toLinearMap := by
      simpa only [LinearMap.baseChange_comp, LinearEquiv.coe_baseChange] using
        congrArg (LinearMap.baseChange ℂ) (g32y_scalar_trans r e a)
    change (r.baseChange ℚ ℂ _ _).toLinearMap
      ((cyc_scalar (r.trans e) a).baseChange ℂ x) ∈
        (cohomologyHodgePiece (g32x_J D t) 1 pq).comap (V.subtype.baseChange ℂ)
    have hc' := LinearMap.congr_fun hc x
    simp only [LinearMap.comp_apply] at hc'
    rw [hc']
    exact hh
  have hsig (σ : cyc_Field S.m →ₐ[ℚ] ℂ) :
      Module.finrank ℂ ↥(cyc_eigenspace (r.trans e) σ ⊓ cohomologyHodgePiece P 1 (1, 0)) = k := by
    rw [g32y_eigenspace_trans, ← hH (1, 0), ← Submodule.comap_inf]
    rw [((r.baseChange ℚ ℂ _ _).ofSubmodule' _).finrank_eq]
    exact hs σ
  refine ⟨{
    P := P
    incl := i
    proj := q
    incl_hom := hi
    proj_hom := hq
    N := N
    N_pos := hN
    retract := hr
    k := k
    act := ⟨S.three_le, hk, r.trans e, hpres, hsig⟩
    equivariant := ?_
    image := hR
  }⟩
  intro h
  change homPullback q 1 ∘ₗ cyc_scalar (r.trans e) (g32p_fieldValue S h) = _
  rw [← hsub, LinearMap.comp_assoc, g32y_scalar_trans,
    ← LinearMap.comp_assoc, he, LinearMap.comp_assoc]

theorem g32y_cover_aux {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c))) :
    ∃ R : g32p_Cover (b65z_fiber D B t), R.J = g32x_J D t := by
  classical
  obtain ⟨f, hf⟩ := g32x_deck_realization D t
  obtain ⟨h1, hmul⟩ := g32x_deck_laws D t f hf
  obtain ⟨hn, hp, hinv⟩ := g32x_theta_invariant D t f hf
  obtain ⟨i, q, N, hN, hi, hq, hr, hz, hR, a, ha, hw⟩ :=
    g32y_marked_comparison_aux D t hg B f hf
  have hd : Module.finrank ℚ (HQ (b65z_fiber D B t).X 1) = 12 := by
    rw [(torusCohomology_cupProductOf (b65z_fiber D B t).X).finrank_eq]
    let := Module.Free.of_basis B
    let := Module.Finite.of_basis B
    have W := b63e_weight_one_riemann c D.C D.hC (b6t_polydisc c)
      (Set.Subset.refl _) D.hG D.atlas.hb D.atlas.f D.atlas.hf D.atlas.hsurj
      D.hk D.Q₀ D.hQ₀ D.Q D.hQ D.P D.hP (b65z_s₀ c) t
    have h := b63g_model_finrank _ _ W.1 _ W.2
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin] at h
    exact h.symm
  refine ⟨{
    J := g32x_J D t
    aut := fun a ↦ (f a).hom
    aut_hom := fun a ↦ (f a).isMonHom
    aut_one := h1
    aut_mul := hmul
    mult := g32x_multiplicity D t hg f hf
    pol := g32x_theta D t
    pol_nondeg := hn
    pol_pos := hp
    pol_inv := hinv
    inclA := i
    projA := q
    inclA_hom := hi
    projA_hom := hq
    NA := N
    NA_pos := hN
    retractA := hr
    groupRing := hz
    rhoBlock := ?_
    dimA := hd
    centre := a
    centre_eq := ha
    weil := hw
    part := fun S hS ↦ Classical.choice (g32y_part_aux D t hg f hf S hS)
  }, rfl⟩
  intro x
  apply g32x_rho_image D t f hf
  rw [← hR]
  exact ⟨x, rfl⟩

end HodgeLean.Foundations.Program
