import HodgeLean.Foundations.Program.SchoenSelectedGeometrySupplierPrimitiveModels
import HodgeLean.Foundations.Program.SchoenSelectedGeometryBranchEnumeration
import HodgeLean.Foundations.Program.SchoenSelectedGeometryPartRetraction
import HodgeLean.Foundations.Program.SchoenSelectedGeometrySupplierCurve
import HodgeLean.Foundations.Program.G32SelectedRealizationSecond
import HodgeLean.Foundations.Program.G32SelectedProp46
import HodgeLean.Foundations.Program.RiemannSurfaceQuotient
import HodgeLean.Adapters.CycleClassPullbackDefs
import HodgeLean.Foundations.Program.UniversalFamilyB60cIsogeny
import HodgeLean.Foundations.Program.CycleFoundationsPullback

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
open scoped Manifold ContDiff TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.fibreFaithful b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

theorem s0_cover_aux {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c))) :
    ∃ (f : g32p_G → AbelianEnd (g32x_J D t))
      (R : g32p_Cover (b65z_fiber D B t)),
      (∀ a, homPullback (f a).hom 1 = g32x_deck D t a) ∧
      R.J = g32x_J D t ∧ HEq R.aut (fun a ↦ (f a).hom) ∧
      HEq R.pol (g32x_theta D t) ∧
      HEq (LinearMap.range (homPullback R.projA 1))
        (LinearMap.range (g32x_projector D t)) := by
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
  refine ⟨f, {
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
  }, hf, rfl, HEq.rfl, HEq.rfl, heq_of_eq hR⟩
  intro x
  apply g32x_rho_image D t f hf
  rw [← hR]
  exact ⟨x, rfl⟩



theorem s0_part_cross_bijective
    (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J] [IsIntegral J.left]
    [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier) (P Q : g32p_Part J aut S) :
    Function.Bijective (homPullback (P.incl ≫ Q.proj) 1) := by
  rw [spec_homPullback_comp]
  have hN : (P.N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr P.N_pos.ne'
  have hr (x : HQ P.P 1) :
      homPullback P.incl 1 (homPullback P.proj 1 x) = (P.N : ℚ) • x :=
    LinearMap.congr_fun (s0_part_retract J aut S P) x
  have hR : LinearMap.range (homPullback Q.proj 1) =
      LinearMap.range (homPullback P.proj 1) := Q.image.trans P.image.symm
  constructor
  · intro x y h
    apply (s0_part_proj_injective J aut S Q)
    have he (v : HQ Q.P 1) :
        homPullback P.proj 1 ((P.N : ℚ) •
          (homPullback P.incl 1 (homPullback Q.proj 1 v))) =
          (P.N : ℚ) ^ 2 • homPullback Q.proj 1 v := by
      have hm : homPullback Q.proj 1 v ∈ LinearMap.range (homPullback P.proj 1) := by
        rw [← hR]; exact LinearMap.mem_range_self _ v
      obtain ⟨w, hw⟩ := hm
      rw [← hw, hr, map_smul, map_smul, smul_smul, pow_two]
    have hh := congrArg (fun v : HQ P.P 1 ↦ homPullback P.proj 1 ((P.N : ℚ) • v)) h
    change homPullback P.proj 1 ((P.N : ℚ) •
      (homPullback P.incl 1 (homPullback Q.proj 1 x))) =
      homPullback P.proj 1 ((P.N : ℚ) •
      (homPullback P.incl 1 (homPullback Q.proj 1 y))) at hh
    rw [he, he] at hh
    exact smul_right_injective _ (pow_ne_zero 2 hN) hh
  · intro x
    have hm : homPullback P.proj 1 ((P.N : ℚ)⁻¹ • x) ∈
        LinearMap.range (homPullback Q.proj 1) := by
      rw [hR]; exact LinearMap.mem_range_self _ _
    obtain ⟨y, hy⟩ := hm
    refine ⟨y, ?_⟩
    change homPullback P.incl 1 (homPullback Q.proj 1 y) = x
    rw [hy, hr, smul_smul, mul_inv_cancel₀ hN, one_smul]

theorem s0_part_cross_proj
    (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J] [IsIntegral J.left]
    [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier) (P Q : g32p_Part J aut S) :
    homPullback P.proj 1 ∘ₗ homPullback (P.incl ≫ Q.proj) 1 =
      (P.N : ℚ) • homPullback Q.proj 1 := by
  rw [spec_homPullback_comp]
  ext v
  have hm : homPullback Q.proj 1 v ∈ LinearMap.range (homPullback P.proj 1) := by
    rw [P.image, ← Q.image]; exact LinearMap.mem_range_self _ v
  obtain ⟨w, hw⟩ := hm
  change homPullback P.proj 1 (homPullback P.incl 1 (homPullback Q.proj 1 v)) =
    (P.N : ℚ) • homPullback Q.proj 1 v
  rw [← hw]
  have hr := LinearMap.congr_fun (s0_part_retract J aut S P) w
  change homPullback P.incl 1 (homPullback P.proj 1 w) = (P.N : ℚ) • w at hr
  rw [hr, map_smul]

theorem s0_part_proj_aeval
    (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J] [IsIntegral J.left]
    [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier) (P : g32p_Part J aut S)
    {h : S.H} (hh : g32p_fieldValue S h = g32p_zeta S) (p : Polynomial ℚ) :
    homPullback P.proj 1 ∘ₗ cyc_scalar P.act.cyc_coordinates
      (Polynomial.aeval (g32p_zeta S) p) =
      Polynomial.aeval (homPullback (aut h) 1) p ∘ₗ homPullback P.proj 1 := by
  have h1 := P.equivariant h
  rw [hh] at h1
  rw [show cyc_scalar P.act.cyc_coordinates (Polynomial.aeval (g32p_zeta S) p) =
    Polynomial.aeval (cyc_scalar P.act.cyc_coordinates (g32p_zeta S)) p from
      (Polynomial.aeval_algHom_apply (cyc_rep P.act.cyc_coordinates) _ _).symm]
  exact g32rep_aeval_intertwine _ h1 p

/-- Any two primitive images of the same action are related by the displayed cross map.
Source: Birkenhake–Lange, Complex Abelian Varieties, §5.3; G32 v0.16, §4.1. -/
theorem s0_part_isogeny_aux
    (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J] [IsIntegral J.left]
    [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier)
    (P Q : g32p_Part J aut S) :
    IsMonHom (P.incl ≫ Q.proj) ∧ ccm2_IsogenyOnPoints (P.incl ≫ Q.proj) ∧
      Function.Bijective (homPullback (P.incl ≫ Q.proj) 1) ∧ P.k = Q.k ∧
      ∀ a : cyc_Field S.m,
        homPullback (P.incl ≫ Q.proj) 1 ∘ₗ cyc_scalar Q.act.cyc_coordinates a =
          cyc_scalar P.act.cyc_coordinates a ∘ₗ homPullback (P.incl ≫ Q.proj) 1 := by
  classical
  letI := P.incl_hom
  letI := Q.proj_hom
  have hb := s0_part_cross_bijective J aut S P Q
  let E := LinearEquiv.ofBijective (homPullback (P.incl ≫ Q.proj) 1) hb
  have hk : P.k = Q.k := by
    have hd := E.finrank_eq
    have hp := P.act.cyc_coordinates.finrank_eq
    have hq := Q.act.cyc_coordinates.finrank_eq
    simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at hp hq
    have hf : 0 < Module.finrank ℚ (cyc_Field S.m) := Module.finrank_pos
    nlinarith
  refine ⟨inferInstance, b60c_isogeny_of_equiv P.P Q.P _ E rfl, hb, hk, ?_⟩
  intro a
  obtain ⟨p, rfl⟩ := g32rep_exists_aeval_zeta S a
  obtain ⟨h, _, hh⟩ := g32rep_exists_gen S
  apply (LinearMap.cancel_left (s0_part_proj_injective J aut S P)).mp
  have hp := s0_part_proj_aeval J aut S P hh p
  have hq := s0_part_proj_aeval J aut S Q hh p
  have hc := s0_part_cross_proj J aut S P Q
  calc
    _ = (homPullback P.proj 1 ∘ₗ homPullback (P.incl ≫ Q.proj) 1) ∘ₗ
        cyc_scalar Q.act.cyc_coordinates (Polynomial.aeval (g32p_zeta S) p) :=
      (LinearMap.comp_assoc _ _ _).symm
    _ = (P.N : ℚ) • (Polynomial.aeval (homPullback (aut h) 1) p ∘ₗ
        homPullback Q.proj 1) := by rw [hc, LinearMap.smul_comp, hq]
    _ = Polynomial.aeval (homPullback (aut h) 1) p ∘ₗ
        (homPullback P.proj 1 ∘ₗ homPullback (P.incl ≫ Q.proj) 1) := by
      rw [hc, LinearMap.comp_smul]
    _ = _ := by rw [← LinearMap.comp_assoc, ← hp, LinearMap.comp_assoc]

theorem s0_wedges_map
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    {m n : ℕ} (e : V ≃ₗ[ℚ] (Fin n → cyc_Field m))
    (d : W ≃ₗ[ℚ] (Fin n → cyc_Field m)) (f : V →ₗ[ℚ] W)
    (hf : ∀ a, f ∘ₗ cyc_scalar e a = cyc_scalar d a ∘ₗ f) :
    (cyc_wedges e).map (exteriorPower.map n f) ≤ cyc_wedges d := by
  have he (t : cyc_Field m →ₐ[ℚ] ℂ) (x : ℂ ⊗[ℚ] V)
      (hx : x ∈ cyc_eigenspace e t) : f.baseChange ℂ x ∈ cyc_eigenspace d t := by
    simp only [cyc_eigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hx ⊢
    intro a
    have h := congrArg (LinearMap.baseChange ℂ) (hf a)
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at h
    have hv := LinearMap.congr_fun h x
    simp only [LinearMap.comp_apply] at hv
    rw [← hv, hx, map_smul]
  have hl (t : cyc_Field m →ₐ[ℚ] ℂ) :
      cyc_line e t ≤ (cyc_line d t).comap (exteriorPower.map n (f.baseChange ℂ)) := by
    rintro _ ⟨w, rfl⟩
    let F : cyc_eigenspace e t →ₗ[ℂ] cyc_eigenspace d t :=
      ((f.baseChange ℂ).comp (cyc_eigenspace e t).subtype).codRestrict _
        (fun x ↦ he t x x.property)
    refine ⟨exteriorPower.map n F w, ?_⟩
    change ((exteriorPower.map n (cyc_eigenspace d t).subtype).comp
      (exteriorPower.map n F)) w =
      ((exteriorPower.map n (f.baseChange ℂ)).comp
        (exteriorPower.map n (cyc_eigenspace e t).subtype)) w
    rw [← exteriorPower.map_comp, ← exteriorPower.map_comp]
    rfl
  have ht : cyc_topLines e ≤
      (cyc_topLines d).comap (exteriorPower.map n (f.baseChange ℂ)) := by
    apply iSup_le
    intro t
    exact (hl t).trans (Submodule.comap_mono (le_iSup (cyc_line d) t))
  rintro _ ⟨w, hw, rfl⟩
  change HodgeBlocks.complexifyWedge n (exteriorPower.map n f w) ∈ cyc_topLines d
  rw [HodgeBlocks.complexifyWedge_exteriorPower_map]
  exact ht hw

theorem s0_wedges_preimage
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    {m n : ℕ} (e : V ≃ₗ[ℚ] (Fin n → cyc_Field m))
    (d : W ≃ₗ[ℚ] (Fin n → cyc_Field m)) (E : V ≃ₗ[ℚ] W)
    (hf : ∀ a, E.toLinearMap ∘ₗ cyc_scalar e a = cyc_scalar d a ∘ₗ E.toLinearMap)
    {w : ⋀[ℚ]^n W} (hw : w ∈ cyc_wedges d) :
    ∃ v ∈ cyc_wedges e, exteriorPower.map n E.toLinearMap v = w := by
  have hi : ∀ a, E.symm.toLinearMap ∘ₗ cyc_scalar d a =
      cyc_scalar e a ∘ₗ E.symm.toLinearMap := by
    intro a
    ext x
    apply E.injective
    have h := LinearMap.congr_fun (hf a) (E.symm x)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, E.apply_symm_apply] using h.symm
  refine ⟨exteriorPower.map n E.symm.toLinearMap w,
    s0_wedges_map d e E.symm.toLinearMap hi (Submodule.mem_map_of_mem hw), ?_⟩
  change ((exteriorPower.map n E.toLinearMap).comp
    (exteriorPower.map n E.symm.toLinearMap)) w = w
  rw [← exteriorPower.map_comp,
    show E.toLinearMap.comp E.symm.toLinearMap = LinearMap.id from by
      ext x; exact E.apply_symm_apply x,
    exteriorPower.map_id]
  rfl

theorem s0_algebraic_pullback
    (X Y : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    {m k l : ℕ} (e : HQ X 1 ≃ₗ[ℚ] (Fin (2 * k) → cyc_Field m))
    (d : HQ Y 1 ≃ₗ[ℚ] (Fin (2 * l) → cyc_Field m))
    (f : Y ⟶ X) [IsMonHom f]
    (hb : Function.Bijective (homPullback f 1))
    (hf : ∀ a, homPullback f 1 ∘ₗ cyc_scalar e a = cyc_scalar d a ∘ₗ homPullback f 1)
    (hk : k = l) (h : cyc_Algebraic (cupProductOf X) e) : cyc_Algebraic (cupProductOf Y) d := by
  subst l
  rintro _ ⟨w, hw, rfl⟩
  let E := LinearEquiv.ofBijective (homPullback f 1) hb
  obtain ⟨v, hv, he⟩ := s0_wedges_preimage e d E hf hw
  rw [← he]
  have hc := LinearMap.congr_fun (spec_homPullback_cupWedgeMap f (2 * k)) v
  change homPullback f (2 * k) ((cupProductOf X).cupWedgeMap (2 * k) v) =
    (cupProductOf Y).cupWedgeMap (2 * k) (exteriorPower.map (2 * k) E.toLinearMap v) at hc
  rw [← hc]
  exact cfd_hom_pullback_span X Y f k _ (h (Submodule.mem_map_of_mem hv))

/-- Algebraicity is invariant under all primitive-image, retraction and coordinate choices.
The statement compares the full determinant spaces, not a chosen generator.
Source: Schoen (1988), Corollary 3.1; Fulton, Intersection Theory, §1.7 and §19.1;
Birkenhake–Lange, Complex Abelian Varieties, §5.3. -/
theorem s0_part_algebraic_iff_aux
    (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J] [IsIntegral J.left]
    [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier)
    (P Q : g32p_Part J aut S) :
    cyc_Algebraic (cupProductOf P.P) P.act.cyc_coordinates ↔
      cyc_Algebraic (cupProductOf Q.P) Q.act.cyc_coordinates := by
  obtain ⟨_, _, hb, hk, hf⟩ := s0_part_isogeny_aux J aut S P Q
  obtain ⟨_, _, hb', _, hf'⟩ := s0_part_isogeny_aux J aut S Q P
  letI := P.incl_hom
  letI := P.proj_hom
  letI := Q.incl_hom
  letI := Q.proj_hom
  haveI : IsMonHom (P.incl ≫ Q.proj) := inferInstance
  haveI : IsMonHom (Q.incl ≫ P.proj) := inferInstance
  exact ⟨s0_algebraic_pullback P.P Q.P P.act.cyc_coordinates Q.act.cyc_coordinates
      (Q.incl ≫ P.proj) hb' hf' hk,
    s0_algebraic_pullback Q.P P.P Q.act.cyc_coordinates P.act.cyc_coordinates
      (P.incl ≫ Q.proj) hb hf hk.symm⟩

/-- Explicit-family successor retaining the actual deck action and image comparison.
Source: G32 v0.16, Proposition 4.6; `g32c_weilLine_algebraic`,
`g32h46_weilAlg_of_line_aux`, `b65z_IsLocalPrym`. -/
theorem s0_prop46_aux {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c)))
    (P : g32h_PrymFamily) (hP : b65z_IsLocalPrym D B P)
    (X : ∀ t : b6t_polydisc c, g32p_Cover (b65z_fiber D B t))
    (f : ∀ t : b6t_polydisc c, g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ t a, homPullback (f t a).hom 1 = g32x_deck D t a)
    (hJ : ∀ t, (X t).J = g32x_J D t)
    (hdeck : ∀ t, HEq (X t).aut (fun a ↦ (f t a).hom))
    (hpol : ∀ t, HEq (X t).pol (g32x_theta D t))
    (himage : ∀ t, HEq (LinearMap.range (homPullback (X t).projA 1))
      (LinearMap.range (g32x_projector D t))) :
    ∀ (_hS : ∀ t, g32p_SchoenSupplier (X t))
      (_hM : ∀ t, g32p_MilneInvariance (X t).J (X t).pol
        (X t).pol_nondeg (X t).pol_pos)
    (_hComparison : ∃ (S : Fin 51 → g32p_Supplier) (χc : ∀ i, (S i).H →* ℂˣ)
      (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G),
      (∀ j, Simple (τ j) ∧ Simple (τbar j) ∧ ¬ g32p_SelfDual (τ j) ∧
        (∀ g, (τbar j).character g = star ((τ j).character g)) ∧ 0 < g32p_cwMult (τ j)) ∧
      (∀ j, Simple (θ j) ∧ g32p_Quaternionic (θ j) ∧ 0 < g32p_cwMult (θ j)) ∧
      (∀ j k, j ≠ k → IsEmpty (τ j ≅ τ k) ∧ IsEmpty (τ j ≅ τbar k)) ∧
      (∀ j k : Fin 4, j ≠ k → IsEmpty (θ j ≅ θ k)) ∧
      Nonempty (τ 2 ≅ g32p_rho) ∧
      (∀ σ : FDRep ℂ g32p_G, Simple σ → 0 < g32p_cwMult σ →
        (¬ g32p_SelfDual σ → ∃ j, Nonempty (σ ≅ τ j) ∨ Nonempty (σ ≅ τbar j)) ∧
        (g32p_Quaternionic σ → ∃ j, Nonempty (σ ≅ θ j))) ∧
      ∀ i : Fin 51,
        (∀ h, ((χc i h : ℂˣ) : ℂ) =
          g32p_root (S i).m ^ (Multiplicative.toAdd ((S i).χ h)).val) ∧
        (∃ r ∈ g32WitnessTable, r.i = i.val + 1 ∧ r.m = (S i).m ∧
          r.orderH = Nat.card (S i).H ∧ (g32p_exponents (S i)).Perm (expandExps r.exps)) ∧
        ∃ v ∈ g32VectorTable, v.i = i.val + 1 ∧
          papersA τ τbar θ (S i).H (χc i) = g32SparseVec v.coords),
    g32s_Prop46 P := by
  intro hS hM hComparison
  obtain ⟨j, hj⟩ := hP
  intro s
  let t := j.symm s
  have heq : P.fiber s = b65z_fiber D B t := by
    simpa only [t, j.apply_symm_apply] using (hj t).2
  rw [heq]
  have hp : g32h_h10 (b65z_fiber D B t) = 3 := by
    rw [← (hj t).2]
    exact (g32h_h10_eq_three P (j t)).1
  apply g32h46_weilAlg_of_line_aux _ 3 hp
  exact g32c_weilLine_algebraic (b65z_fiber D B t) (X t) (hS t) (hM t)
    (hComparison := hComparison)
    (hAdmissible := g32c_supplier_admissible (b65z_fiber D B t) (X t))
    (hEmbedding := g32c_embedding_exists)
    (hComplement := fun S hS' u ↦
      g32c_coLine_ne_bot ((X t).part S hS').act.cyc_coordinates u)
    (hProduct := g32c_schoen_product_span (b65z_fiber D B t) (X t))
    (hDegree := g32c_degree_count (b65z_fiber D B t) (X t))

/-- Algebraic supplier quotients with local monodromy and the exact primitive comparison.
Source: G32 v0.16, §4.1; Miranda, Algebraic Curves and Riemann Surfaces,
Ch. III, Theorem 3.4; Birkenhake–Lange, Complex Abelian Varieties, §11.4 and Ch. 12. -/
theorem s0_supplier_algebraic_aux {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (S : g32p_Supplier)
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a) :
    let C := b65z_fibre c D.C t
    let Y := rsq_Quot S.χ.ker C
    let Z := rsq_Quot S.H C
    ∃ (C₀ Y₀ Z₀ : Over (Spec ↧ℂ)),
      ∃ (_ : IsIntegral C₀.left) (_ : Smooth C₀.hom) (_ : IsProjective C₀.hom),
      ∃ (_ : IsIntegral Y₀.left) (_ : Smooth Y₀.hom) (_ : IsProjective Y₀.hom),
      ∃ (_ : IsIntegral Z₀.left) (_ : Smooth Z₀.hom) (_ : IsProjective Z₀.hom),
      TopologicalSpace.dim C₀.left = 1 ∧ TopologicalSpace.dim Y₀.left = 1 ∧
      TopologicalSpace.dim Z₀.left = 1 ∧
      ∃ (q : C₀ ⟶ Y₀) (p : Y₀ ⟶ Z₀) (j : C₀ ⟶ g32x_J D t)
        (a : (S.H ⧸ S.χ.ker) → (Y₀ ⟶ Y₀))
        (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
        (eC : C ≃ₜ ComplexPoint C₀) (eY : Y ≃ₜ ComplexPoint Y₀)
        (eZ : Z ≃ₜ ComplexPoint Z₀),
      (∀ h : S.H, e (QuotientGroup.mk h) = S.χ h) ∧
      a 1 = 𝟙 Y₀ ∧ (∀ u v, a (u * v) = a v ≫ a u) ∧
      Function.Injective a ∧ (∀ u, a u ≫ p = p) ∧
      (∀ x, Point.map q (eC x) = eY (rsq_proj S.χ.ker C x)) ∧
      (∀ y, Point.map p (eY y) = eZ (rsq_coarsen S.χ.ker y)) ∧
      (∀ u y, Point.map (a u) (eY y) = eY (u • y)) ∧
      Function.Bijective (homPullback j 1) ∧
      ∃ cy : ChartedSpace ℂ Y, ∃ cz : ChartedSpace ℂ Z,
        letI := cy
        letI := cz
        ∃ (_ : IsManifold 𝓘(ℂ, ℂ) ω Y) (_ : IsManifold 𝓘(ℂ, ℂ) ω Z),
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim C₀.left) → ℂ) ω eC ∧
        ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim C₀.left) → ℂ) 𝓘(ℂ, ℂ) ω eC.symm ∧
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim Y₀.left) → ℂ) ω eY ∧
        ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim Y₀.left) → ℂ) 𝓘(ℂ, ℂ) ω eY.symm ∧
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim Z₀.left) → ℂ) ω eZ ∧
        ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim Z₀.left) → ℂ) 𝓘(ℂ, ℂ) ω eZ.symm ∧
        (∃ (y : Fin (g32p_exponents S).length → Y)
          (r : Fin (g32p_exponents S).length → S.H ⧸ S.χ.ker),
          Function.Injective (fun i ↦ rsq_coarsen S.χ.ker (y i)) ∧
          (∀ i, b4_IsRotGen ℂ (y i) (r i) ∧
            e (r i) = Multiplicative.ofAdd ((g32p_exponents S)[i] : ZMod S.m)) ∧
          (∀ z : Y, MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
            ∃ i, rsq_coarsen S.χ.ker z = rsq_coarsen S.χ.ker (y i))) ∧
        (let V := LinearMap.ker
          (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
            (Polynomial.cyclotomic S.m ℚ))
        ∀ P : g32p_Part (g32x_J D t) (fun h ↦ (f h).hom) S,
          ∃ E : HQ P.P 1 ≃ₗ[ℚ] V,
            (∀ v, homPullback q 1 (E v) = homPullback j 1 (homPullback P.proj 1 v)) ∧
            (∀ (h : S.H) v,
              homPullback (a ((QuotientGroup.mk h)⁻¹)) 1 (E v) =
                (E (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S h) v) : HQ Y₀ 1)) ∧
            Module.finrank ℚ V = 2 * P.k * Nat.totient S.m ∧
            2 * P.k + 2 = 2 * Module.finrank ℂ (b3_HolForm ℂ Z) +
              (g32p_exponents S).length) := by
  classical
  obtain ⟨C₀, Y₀, Z₀, hCi, hCs, hCp, hYi, hYs, hYp, hZi, hZs, hZp,
    hCd, hYd, hZd, q, p, j, a, e, eC, eY, eZ, he, ha1, ham, hai,
    hap, hq', hp', ha, hj, hqi, hqr, hjdeck, cy, cz, hy, hz,
    hC, hCi', hY, hYi', hZ, hZi', hprimitive⟩ :=
      s0_supplier_models_with_primitive D t hg S f hf
  letI := cy
  letI := cz
  letI := hy
  letI := hz
  have hq := s0_model_square_holomorphic C₀ Y₀ eC eY hC hYi' q
    (rsq_proj S.χ.ker (b65z_fibre c D.C t)) hq'
  have hA (u : S.H ⧸ S.χ.ker) := s0_model_square_holomorphic Y₀ Y₀ eY eY hY hYi'
    (a u) (fun y ↦ u • y) (ha u)
  have hbranch := s0_branch_enumeration D t hg S hq hA e he
  exact ⟨C₀, Y₀, Z₀, hCi, hCs, hCp, hYi, hYs, hYp, hZi, hZs, hZp,
    hCd, hYd, hZd, q, p, j, a, e, eC, eY, eZ, he, ha1, ham, hai,
    hap, hq', hp', ha, hj, cy, cz, hy, hz,
    hC, hCi', hY, hYi', hZ, hZi', hbranch, hprimitive⟩

end HodgeLean.Foundations.Program
