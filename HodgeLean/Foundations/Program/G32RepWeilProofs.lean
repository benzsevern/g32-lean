import HodgeLean.Foundations.Program.G32RepTransport
import HodgeLean.Foundations.Program.G32PropFourSixUnitary
import HodgeLean.Foundations.Program.G32PropFourSixDualMultiplicity

/-! # Open bodies for the G32 representation stage H

One auxiliary declaration per statement of `G32RepWeil.lean`: the image of `projA^*` as
`ℓ ⊗ M_ρ ⊕ ℓ̄ ⊗ M_ρ̄`, its preservation by `U`, the Weil eigenspace inside it, the transport of `U`
to the Weil eigenspace with its dimension, and the uniform sign of the determinant there.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

open scoped TensorProduct CategoryTheory.MonObj Matrix
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

variable {A : g32t_Sixfold}

theorem g32rep_inclA_projA (X : g32p_Cover A) :
    homPullback X.inclA 1 ∘ₗ homPullback X.projA 1 =
      (X.NA : ℚ) • LinearMap.id := by
  rw [← spec_homPullback_comp, X.retractA, ← zpow_natCast, spec_homPullback_zpow,
    spec_homPullback_id, Int.cast_natCast]

theorem g32rep_inclA_projA_C (X : g32p_Cover A) (y : ℂ ⊗[ℚ] HQ A.X 1) :
    (homPullback X.inclA 1).baseChange ℂ
        ((homPullback X.projA 1).baseChange ℂ y) = (X.NA : ℂ) • y := by
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, g32rep_inclA_projA,
    LinearMap.baseChange_smul, LinearMap.baseChange_id, LinearMap.smul_apply, LinearMap.id_apply]
  exact (algebraMap_smul ℂ (X.NA : ℚ) y).symm.trans (by simp)

theorem g32rep_projA_injective (X : g32p_Cover A) :
    Function.Injective ((homPullback X.projA 1).baseChange ℂ) := by
  intro y z hyz
  have hN : (X.NA : ℂ) ≠ 0 := Nat.cast_ne_zero.2 X.NA_pos.ne'
  have he := congrArg ((homPullback X.inclA 1).baseChange ℂ) hyz
  rw [g32rep_inclA_projA_C, g32rep_inclA_projA_C] at he
  exact smul_right_injective _ hN he

theorem g32rep_projA_range_comp (X : g32p_Cover A) :
    LinearMap.range ((homPullback X.projA 1).baseChange ℂ ∘ₗ
      (homPullback X.inclA 1).baseChange ℂ) =
      LinearMap.range ((homPullback X.projA 1).baseChange ℂ) := by
  apply le_antisymm
  · exact LinearMap.range_comp_le_range _ _
  · rintro _ ⟨y, rfl⟩
    refine ⟨(X.NA : ℂ)⁻¹ • (homPullback X.projA 1).baseChange ℂ y, ?_⟩
    rw [LinearMap.comp_apply, map_smul, g32rep_inclA_projA_C, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 X.NA_pos.ne'), one_smul]

theorem g32rep_projA_commute (X : g32p_Cover A)
    {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)} (hu : u ∈ g32c_U X) :
    u ∘ₗ ((homPullback X.projA 1).baseChange ℂ ∘ₗ
      (homPullback X.inclA 1).baseChange ℂ) =
    ((homPullback X.projA 1).baseChange ℂ ∘ₗ
      (homPullback X.inclA 1).baseChange ℂ) ∘ₗ u := by
  obtain ⟨c, hc⟩ := X.groupRing
  rw [← LinearMap.baseChange_comp, ← spec_homPullback_comp, hc]
  have hprod : homPullback (∏ g, X.aut g ^ c g) 1 =
      ∑ g, homPullback (X.aut g ^ c g) 1 := by
    induction (Finset.univ : Finset g32p_G) using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty, spec_homPullback_one]
    | insert g s hg ih =>
      rw [Finset.prod_insert hg, Finset.sum_insert hg, spec_homPullback_mul, ih]
  rw [hprod]
  induction (Finset.univ : Finset g32p_G) using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, LinearMap.baseChange_zero,
      LinearMap.comp_zero, LinearMap.zero_comp]
  | insert g t hg ih =>
    rw [Finset.sum_insert hg, LinearMap.baseChange_add, LinearMap.comp_add,
      LinearMap.add_comp, ih, spec_homPullback_zpow, LinearMap.baseChange_smul,
      LinearMap.comp_smul, LinearMap.smul_comp, hu.2.1 g]


theorem g32rep_weil_intertwine (X : g32p_Cover A) (y : ℂ ⊗[ℚ] HQ A.X 1) :
    (homPullback X.projA 1).baseChange ℂ (A.W.Jc y) =
      (homPullback X.projA 1).baseChange ℂ y +
        (2 : ℂ) • g32rep_rep X X.centre ((homPullback X.projA 1).baseChange ℂ y) := by
  have he : homPullback X.projA 1 ∘ₗ A.W.J =
      homPullback X.projA 1 + (2 : ℚ) •
        (homPullback (X.aut X.centre) 1 ∘ₗ homPullback X.projA 1) := by
    ext x
    exact X.weil x
  have hec := congrArg (fun f => f.baseChange ℂ) he
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_add, LinearMap.baseChange_smul,
    LinearMap.baseChange_comp] at hec
  have h := LinearMap.congr_fun hec y
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] at h
  rw [← algebraMap_smul ℂ (2 : ℚ)] at h
  norm_num only [map_ofNat] at h
  exact h

theorem g32rep_simple_map_injective {G : Type} [Group G] [Fintype G]
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (σ : FDRep ℂ G) [Simple σ] (ρ : Representation ℂ G V)
    (φ : σ →ₗ[ℂ] V) (hφ : φ ∈ rfd_mult σ ρ) (h0 : φ ≠ 0) :
    Function.Injective φ := by
  let F : σ ⟶ FDRep.of ρ :=
    ⟨InducedCategory.homMk (ModuleCat.ofHom φ), fun g => by
      ext x
      exact LinearMap.congr_fun (hφ g) x⟩
  have hF : F ≠ 0 := by
    intro h
    apply h0
    ext x
    have ht := congrArg (fun f : σ ⟶ FDRep.of ρ => f.hom.hom.hom x) h
    change φ x = _ at ht
    exact ht.trans (by rfl)
  haveI : Mono F := mono_of_nonzero_from_simple hF
  haveI : Mono ((forget₂ (FDRep ℂ G) (Rep ℂ G)).map F) := inferInstance
  exact (Rep.mono_iff_injective ((forget₂ (FDRep ℂ G) (Rep ℂ G)).map F)).mp inferInstance

theorem g32rep_eval_injective {G : Type} [Group G] [Fintype G]
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (σ : FDRep ℂ G) [Simple σ] (ρ : Representation ℂ G V) (x : σ) (hx : x ≠ 0) :
    Function.Injective ((LinearMap.applyₗ x).domRestrict (rfd_mult σ ρ)) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro φ hφ
  have he : (φ : σ →ₗ[ℂ] V) x = 0 := hφ
  have hzero : (φ : σ →ₗ[ℂ] V) = 0 := by
    by_contra h
    exact hx (g32rep_simple_map_injective σ ρ φ φ.2 h (he.trans (map_zero _).symm))
  exact Subtype.ext hzero

theorem g32rep_eval_range_preserved {G : Type} [Group G] [Fintype G]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (σ : FDRep ℂ G) (ρ : Representation ℂ G V) (x : σ)
    (u : Module.End ℂ V) (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ)) :
    ∀ z ∈ LinearMap.range ((LinearMap.applyₗ x).domRestrict (rfd_mult σ ρ)),
      u z ∈ LinearMap.range ((LinearMap.applyₗ x).domRestrict (rfd_mult σ ρ)) := by
  rintro _ ⟨φ, rfl⟩
  exact ⟨rfd_multAct σ ρ u hu φ, rfl⟩

theorem g32rep_det_eval_range {G : Type} [Group G] [Fintype G]
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (σ : FDRep ℂ G) [Simple σ] (ρ : Representation ℂ G V) (x : σ) (hx : x ≠ 0)
    (u : Module.End ℂ V) (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ)) :
    LinearMap.det (u.restrict (g32rep_eval_range_preserved σ ρ x u hu)) =
      rfd_det σ ρ u hu := by
  let f := (LinearMap.applyₗ x).domRestrict (rfd_mult σ ρ)
  let e := LinearEquiv.ofInjective f (g32rep_eval_injective σ ρ x hx)
  have he : u.restrict (g32rep_eval_range_preserved σ ρ x u hu) =
      (e : _ →ₗ[ℂ] _) ∘ₗ rfd_multAct σ ρ u hu ∘ₗ (e.symm : _ →ₗ[ℂ] _) := by
    ext z
    change u (z : V) = f (rfd_multAct σ ρ u hu (e.symm z))
    change u (z : V) = u (f (e.symm z))
    exact congrArg u (congrArg Subtype.val (e.apply_symm_apply z)).symm
  rw [he, LinearMap.det_conj]
  rfl

theorem g32rep_rho_centre (X : g32p_Cover A) {c : ℂ}
    (hc : b4b_toMatrix X.centre = c • 1) :
    g32p_rho.ρ X.centre = c • LinearMap.id := by
  change Matrix.toLin' (b4b_toMatrix X.centre) = _
  rw [hc, map_smul, Matrix.toLin'_one]
  rfl

theorem g32rep_dual_scalar {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (g : G) {c : ℂ} (hc : c ≠ 0)
    (hρ : ρ g = c • LinearMap.id) :
    ρ.dual g = c⁻¹ • LinearMap.id := by
  have hi : ∀ v, ρ g⁻¹ v = c⁻¹ • v := by
    intro v
    apply smul_right_injective _ hc
    change c • (ρ g⁻¹ v) = c • (c⁻¹ • v)
    have he : c • (ρ g⁻¹ v) = v := by
      have h := congrArg (fun f : Module.End ℂ V => f v) (ρ.map_mul g g⁻¹)
      rw [mul_inv_cancel, map_one] at h
      change v = ρ g (ρ g⁻¹ v) at h
      rw [hρ] at h
      exact h.symm
    rw [he, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [Representation.dual_apply]
  ext φ v
  change φ (ρ g⁻¹ v) = c⁻¹ • φ v
  rw [hi, map_smul]

theorem g32rep_eval_scalar {G : Type} [Group G] [Fintype G]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (σ : FDRep ℂ G) (ρ : Representation ℂ G V) (g : G) {c : ℂ}
    (hc : σ.ρ g = c • LinearMap.id) (x : σ) :
    (rfd_mult σ ρ).map (LinearMap.applyₗ x) ≤ Module.End.eigenspace (ρ g) c := by
  rintro _ ⟨φ, hφ, rfl⟩
  apply Module.End.mem_eigenspace_iff.mpr
  have he := LinearMap.congr_fun (hφ g) x
  rw [hc, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.id_apply, map_smul] at he
  exact he.symm

theorem g32rep_select_eigenspace {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) (P Q : Submodule ℂ V) {c d : ℂ} (hcd : c ≠ d)
    (hP : P ≤ Module.End.eigenspace f c) (hQ : Q ≤ Module.End.eigenspace f d) :
    (P ⊔ Q) ⊓ Module.End.eigenspace f c = P := by
  apply le_antisymm
  · intro z hz
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hz.1
    have hae := Module.End.mem_eigenspace_iff.mp (hP ha)
    have hbe := Module.End.mem_eigenspace_iff.mp (hQ hb)
    have hze := Module.End.mem_eigenspace_iff.mp hz.2
    rw [← hab, map_add, hae, smul_add] at hze
    have hb' := add_left_cancel hze
    have hzero : (d - c) • b = 0 := by
      rw [sub_smul, ← hbe, ← hb', sub_self]
    have hb0 : b = 0 := (smul_eq_zero.mp hzero).resolve_left
      (sub_ne_zero.mpr hcd.symm)
    rw [hb0, add_zero] at hab
    exact hab ▸ ha
  · intro z hz
    exact ⟨Submodule.mem_sup_left hz, hP hz⟩

theorem g32rep_cube_roots {c d : ℂ} (hc : c ^ 2 + c + 1 = 0)
    (hd : d ^ 2 + d + 1 = 0) : c = d ∨ c = d ^ 2 := by
  have he : (c - d) * (c - d ^ 2) = 0 := by
    linear_combination hc + (d - c - 1) * hd
  exact (mul_eq_zero.mp he).imp sub_eq_zero.mp sub_eq_zero.mp

theorem g32rep_cube_root_ne_square {c : ℂ} (hc : c ^ 2 + c + 1 = 0) :
    c ≠ c ^ 2 := by
  intro he
  have hf : c * (c - 1) = 0 := by linear_combination -he
  rcases mul_eq_zero.mp hf with h | h
  · rw [h] at hc
    norm_num at hc
  · rw [sub_eq_zero.mp h] at hc
    norm_num at hc

theorem g32rep_det_transport {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ψ : V →ₗ[ℂ] W) (hψ : Function.Injective ψ)
    (P : Submodule ℂ V) (Q : Submodule ℂ W) (hPQ : P.map ψ = Q)
    (R : Module.End ℂ V) (u : Module.End ℂ W)
    (hR : ∀ y ∈ P, R y ∈ P) (hU : ∀ z ∈ Q, u z ∈ Q)
    (hI : ∀ y, ψ (R y) = u (ψ y)) :
    LinearMap.det (R.restrict hR) = LinearMap.det (u.restrict hU) := by
  let f : P →ₗ[ℂ] Q := (ψ.domRestrict P).codRestrict Q (fun y => by
    rw [← hPQ]
    exact ⟨y, y.2, rfl⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro y z h
      apply Subtype.ext
      exact hψ (congrArg Subtype.val h)
    · intro z
      have hz : (z : W) ∈ P.map ψ := hPQ.symm ▸ z.2
      obtain ⟨y, hy, he⟩ := hz
      exact ⟨⟨y, hy⟩, Subtype.ext he⟩
  let e := LinearEquiv.ofBijective f hf
  have he : R.restrict hR = (e.symm : _ →ₗ[ℂ] _) ∘ₗ
      u.restrict hU ∘ₗ (e.symm.symm : _ →ₗ[ℂ] _) := by
    ext y
    apply hψ
    have hi := congrArg Subtype.val (e.apply_symm_apply (u.restrict hU (e y)))
    change ψ ((e.symm (u.restrict hU (e y)) : P) : V) = u (ψ y) at hi
    exact (hI y).trans hi.symm
  rw [he, LinearMap.det_conj]

theorem g32rep_groupRing_pullback (X : g32p_Cover A) :
    ∃ c : g32p_G → ℤ,
      (homPullback X.projA 1).baseChange ℂ ∘ₗ (homPullback X.inclA 1).baseChange ℂ =
        (∑ g, (c g : ℚ) • homPullback (X.aut g) 1).baseChange ℂ := by
  obtain ⟨c, hc⟩ := X.groupRing
  refine ⟨c, ?_⟩
  rw [← LinearMap.baseChange_comp, ← spec_homPullback_comp, hc]
  congr 1
  induction (Finset.univ : Finset g32p_G) using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, spec_homPullback_one]
  | insert g t hg ih =>
    rw [Finset.prod_insert hg, Finset.sum_insert hg, spec_homPullback_mul, ih,
      spec_homPullback_zpow]

theorem g32rep_projA_groupRing_range (X : g32p_Cover A) :
    ∃ c : g32p_G → ℤ,
      LinearMap.range ((homPullback X.projA 1).baseChange ℂ) =
        LinearMap.range ((∑ g, (c g : ℚ) • homPullback (X.aut g) 1).baseChange ℂ) := by
  obtain ⟨c, hc⟩ := g32rep_groupRing_pullback X
  exact ⟨c, (g32rep_projA_range_comp X).symm.trans (congrArg LinearMap.range hc)⟩

theorem g32rep_rhoBlock_complex (X : g32p_Cover A) (y : ℂ ⊗[ℚ] HQ A.X 1) :
    g32p_rhoProjector X.aut ((homPullback X.projA 1).baseChange ℂ y) =
      (homPullback X.projA 1).baseChange ℂ y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c v =>
    have he := congrArg (fun z => c • z) (X.rhoBlock v)
    rw [← map_smul] at he
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      LinearMap.baseChange_tmul] using he
  | add y z hy hz => rw [map_add, map_add, hy, hz]

theorem g32rep_projA_range_finrank (X : g32p_Cover A) :
    Module.finrank ℂ (LinearMap.range ((homPullback X.projA 1).baseChange ℂ)) = 12 := by
  rw [LinearMap.finrank_range_of_inj (g32rep_projA_injective X),
    Module.finrank_baseChange, X.dimA]

theorem g32rep_mult_finrank (X : g32p_Cover A) (σ : FDRep ℂ g32p_G)
    (hσ : Simple σ) (hnt : ∃ g, σ.ρ g ≠ 1) :
    (Module.finrank ℂ (rfd_mult σ (g32rep_rep X)) : ℂ) = g32p_cwMult σ := by
  have := (torusCohomology_cupProductOf X.J).finite
  rw [(rfd_multEquiv σ (g32rep_rep X)).finrank_eq, rfd_finrank_intertwiningMap,
    ← X.mult σ hσ hnt, g32p_multiplicity]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  change LinearMap.trace ℂ _ (g32rep_rep X g) * σ.character g⁻¹ = _
  rw [← rfd_star_character]
  change LinearMap.trace ℂ _ ((homPullback (X.aut g) 1).baseChange ℂ) * _ = _
  rw [LinearMap.trace_baseChange, eq_ratCast]

theorem g32rep_coeff_trace_vanish (c : g32p_G → ℤ)
    (hE : ∑ g, (c g : ℂ) • b4b_toMatrix g = 0) (k : g32p_G) :
    ∑ g, (c g : ℂ) * (b4b_toMatrix (k * g⁻¹)).trace = 0 := by
  have h : ∑ g, (c g : ℂ) * (b4b_toMatrix (k * g⁻¹)).trace =
      (b4b_toMatrix k * (∑ g, (c g : ℂ) • b4b_toMatrix g)ᴴ).trace := by
    rw [Matrix.conjTranspose_sum, Matrix.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_mul, g32p_group_inverse_matrix, Matrix.conjTranspose_smul, Matrix.mul_smul,
      Matrix.trace_smul, smul_eq_mul, star_intCast]
  rw [h, hE, Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.trace_zero]

theorem g32rep_projector_comp_zero (X : g32p_Cover A) (c : g32p_G → ℤ)
    (hE : ∑ g, (c g : ℂ) • b4b_toMatrix g = 0) :
    g32p_rhoProjector X.aut ∘ₗ (∑ g, (c g : ℂ) • g32rep_rep X g) = 0 := by
  let t : g32p_G → ℂ := fun h => (b4b_toMatrix h).trace + star (b4b_toMatrix h).trace
  have ht : ∀ k, ∑ g, (c g : ℂ) * t (k * g⁻¹) = 0 := by
    intro k
    have h1 := g32rep_coeff_trace_vanish c hE k
    have h2 := congrArg star h1
    rw [star_sum, star_zero] at h2
    simp only [star_mul', star_intCast] at h2
    simp only [t, mul_add, Finset.sum_add_distrib, h1, h2, add_zero]
  have hP : g32p_rhoProjector X.aut =
      ((4 : ℂ) / Fintype.card g32p_G) • ∑ h, t h • g32rep_rep X h := rfl
  rw [hP, LinearMap.smul_comp, ← Module.End.mul_eq_comp, Finset.mul_sum]
  have hs : ∀ g, (∑ h, t h • g32rep_rep X h) * ((c g : ℂ) • g32rep_rep X g) =
      ∑ k, ((c g : ℂ) * t (k * g⁻¹)) • g32rep_rep X k := by
    intro g
    rw [Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h => ?_
    rw [Equiv.coe_mulRight, mul_inv_cancel_right, map_mul, smul_mul_smul_comm, mul_comm]
  simp only [hs]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, ht, zero_smul, Finset.sum_const_zero, smul_zero]

theorem g32rep_groupRing_complex (X : g32p_Cover A) (c : g32p_G → ℤ) :
    (∑ g, (c g : ℚ) • homPullback (X.aut g) 1).baseChange ℂ =
      ∑ g, (c g : ℂ) • g32rep_rep X g := by
  induction (Finset.univ : Finset g32p_G) using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, LinearMap.baseChange_zero]
  | insert g t hg ih =>
    rw [Finset.sum_insert hg, Finset.sum_insert hg, LinearMap.baseChange_add, ih,
      LinearMap.baseChange_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    rfl

theorem g32rep_mult_groupRing {V : Type} [AddCommGroup V] [Module ℂ V]
    (σ : FDRep ℂ g32p_G) (ρ : Representation ℂ g32p_G V) (c : g32p_G → ℤ)
    (φ : σ →ₗ[ℂ] V) (hφ : φ ∈ rfd_mult σ ρ) (v : σ) :
    φ ((∑ g, (c g : ℂ) • σ.ρ g) v) = (∑ g, (c g : ℂ) • ρ g) (φ v) := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← LinearMap.comp_apply, hφ g, LinearMap.comp_apply]

theorem g32rep_scalar_ne_one {V : Type*} [AddCommGroup V] [Module ℂ V] [hV : Nontrivial V]
    (f : Module.End ℂ V) {d : ℂ} (hd : d ≠ 1) (hf : f = d • LinearMap.id) : f ≠ 1 := by
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have he := LinearMap.congr_fun (hf.symm.trans h) v
  rw [LinearMap.smul_apply, LinearMap.id_apply, Module.End.one_apply] at he
  have hz : (d - 1) • v = 0 := by rw [sub_smul, he, one_smul, sub_self]
  exact hv ((smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hd))

theorem g32rep_eval_map_finrank (X : g32p_Cover A) (σ : FDRep ℂ g32p_G) [hσ : Simple σ]
    (hnt : ∃ g, σ.ρ g ≠ 1) (hm : g32p_cwMult σ = 6) (x : σ) (hx : x ≠ 0) :
    Module.finrank ℂ ((rfd_mult σ (g32rep_rep X)).map (LinearMap.applyₗ x)) = 6 := by
  have := (torusCohomology_cupProductOf X.J).finite
  rw [← LinearMap.range_domRestrict,
    LinearMap.finrank_range_of_inj (g32rep_eval_injective σ (g32rep_rep X) x hx)]
  have h := g32rep_mult_finrank X σ hσ hnt
  rw [hm] at h
  exact_mod_cast h

theorem g32rep_rho_groupRing_ne_zero (c : g32p_G → ℤ)
    (hE : ∑ g, (c g : ℂ) • b4b_toMatrix g ≠ 0) :
    ∑ g, (c g : ℂ) • g32p_rho.ρ g ≠ 0 := by
  have h : ∑ g, (c g : ℂ) • g32p_rho.ρ g =
      Matrix.toLin' (∑ g, (c g : ℂ) • b4b_toMatrix g) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul]
    rfl
  rw [h]
  intro h0
  exact hE (Matrix.toLin'.injective (h0.trans (map_zero _).symm))

theorem g32rep_dual_groupRing_zero {G : Type} [Group G] {V : Type} [AddCommGroup V]
    [Module ℂ V] [_i : Module.Free ℂ V] (ρ : Representation ℂ G V) (s : Finset G) (a : G → ℂ)
    (h0 : ∑ g ∈ s, a g • ρ.dual g = 0) : ∑ g ∈ s, a g • ρ g⁻¹ = 0 := by
  refine LinearMap.ext fun w => ?_
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro f
  have he := LinearMap.congr_fun (LinearMap.congr_fun h0 f) w
  rw [LinearMap.zero_apply, LinearMap.zero_apply, LinearMap.sum_apply,
    LinearMap.sum_apply] at he
  rw [LinearMap.sum_apply, map_sum, ← he]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, map_smul,
    Representation.dual_apply]
  rfl

theorem g32rep_rhoDual_groupRing_ne_zero (c : g32p_G → ℤ)
    (hE : ∑ g, (c g : ℂ) • b4b_toMatrix g ≠ 0) :
    ∑ g, (c g : ℂ) • g32p_rhoDual.ρ g ≠ 0 := by
  intro h0
  apply hE
  have hw := g32rep_dual_groupRing_zero (V := Fin 4 → ℂ) g32p_rho.ρ Finset.univ
    (fun g => (c g : ℂ)) h0 (_i := Module.Free.of_divisionRing ℂ _)
  have hl : Matrix.toLin' (∑ g, (c g : ℂ) • (b4b_toMatrix g)ᴴ) = 0 := by
    refine Eq.trans ?_ hw
    rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, ← g32p_group_inverse_matrix]
    rfl
  have hc := congrArg Matrix.conjTranspose (Matrix.toLin'.injective (hl.trans (map_zero _).symm))
  rw [Matrix.conjTranspose_sum, Matrix.conjTranspose_zero] at hc
  simpa only [Matrix.conjTranspose_smul, star_intCast, Matrix.conjTranspose_conjTranspose]
    using hc

theorem g32rep_exists_ne_zero_apply {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (f : V →ₗ[ℂ] W) (hf : f ≠ 0) : ∃ v, f v ≠ 0 := by
  by_contra h
  push Not at h
  exact hf (LinearMap.ext h)

theorem g32rep_projA_range_aux (X : g32p_Cover A) :
    ∃ (x : g32p_rho) (y : g32p_rhoDual), x ≠ 0 ∧ y ≠ 0 ∧
      LinearMap.range ((homPullback X.projA 1).baseChange ℂ) =
        (rfd_mult g32p_rho (g32rep_rep X)).map (LinearMap.applyₗ x) ⊔
          (rfd_mult g32p_rhoDual (g32rep_rep X)).map (LinearMap.applyₗ y) := by
  have := (torusCohomology_cupProductOf X.J).finite
  have := g32p_rho_simple
  have := g32p_rhoDual_simple
  obtain ⟨c, hc⟩ := g32rep_projA_groupRing_range X
  rw [g32rep_groupRing_complex] at hc
  set W := LinearMap.range ((homPullback X.projA 1).baseChange ℂ) with hWdef
  have hE : ∑ g, (c g : ℂ) • b4b_toMatrix g ≠ 0 := by
    intro h0
    have hz := g32rep_projector_comp_zero X c h0
    have hW : W = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨z, rfl⟩
      have hm : (homPullback X.projA 1).baseChange ℂ z ∈ W := LinearMap.mem_range_self _ z
      rw [hc] at hm
      obtain ⟨v, hv⟩ := hm
      rw [Submodule.mem_bot, ← g32rep_rhoBlock_complex, ← hv, ← LinearMap.comp_apply, hz,
        LinearMap.zero_apply]
    have h12 := g32rep_projA_range_finrank X
    rw [← hWdef, hW, finrank_bot] at h12
    exact absurd h12 (by norm_num)
  obtain ⟨v, hv⟩ := g32rep_exists_ne_zero_apply _ (g32rep_rho_groupRing_ne_zero c hE)
  obtain ⟨w, hw⟩ := g32rep_exists_ne_zero_apply _ (g32rep_rhoDual_groupRing_ne_zero c hE)
  set x := (∑ g, (c g : ℂ) • g32p_rho.ρ g) v
  set y := (∑ g, (c g : ℂ) • g32p_rhoDual.ρ g) w
  obtain ⟨d, hd, hmat⟩ := X.centre_eq
  have hd0 : d ≠ 0 := by intro h; rw [h] at hd; norm_num at hd
  have hd1 : d ≠ 1 := by intro h; rw [h] at hd; norm_num at hd
  have hd3 : d * d ^ 2 = 1 := by linear_combination (d - 1) * hd
  have hdi : d⁻¹ = d ^ 2 := inv_eq_of_mul_eq_one_right hd3
  have hd21 : d ^ 2 ≠ 1 := by
    intro h
    have h2 : d = -2 := by linear_combination hd - h
    rw [h2] at h
    norm_num at h
  have hρ := g32rep_rho_centre X hmat
  have hdual : g32p_rhoDual.ρ X.centre = d ^ 2 • LinearMap.id :=
    hdi ▸ g32rep_dual_scalar g32p_rho.ρ X.centre hd0 hρ
  let P := (rfd_mult g32p_rho (g32rep_rep X)).map (LinearMap.applyₗ x)
  let Q := (rfd_mult g32p_rhoDual (g32rep_rep X)).map (LinearMap.applyₗ y)
  have hPW : P ≤ W := by
    rintro _ ⟨φ, hφ, rfl⟩
    rw [hc]
    exact ⟨φ v, (g32rep_mult_groupRing g32p_rho (g32rep_rep X) c φ hφ v).symm⟩
  have hQW : Q ≤ W := by
    rintro _ ⟨φ, hφ, rfl⟩
    rw [hc]
    exact ⟨φ w, (g32rep_mult_groupRing g32p_rhoDual (g32rep_rep X) c φ hφ w).symm⟩
  have hP6 : Module.finrank ℂ P = 6 :=
    g32rep_eval_map_finrank X g32p_rho ⟨X.centre, g32rep_scalar_ne_one (hV := ⟨⟨x, 0, hv⟩⟩) _ hd1 hρ⟩
      g32p_rho_cwMult x hv
  have hQ6 : Module.finrank ℂ Q = 6 :=
    g32rep_eval_map_finrank X g32p_rhoDual ⟨X.centre, g32rep_scalar_ne_one (hV := ⟨⟨y, 0, hw⟩⟩) _ hd21 hdual⟩
      g32p_rhoDual_cwMult y hw
  have hPe := g32rep_eval_scalar g32p_rho (g32rep_rep X) X.centre hρ x
  have hQe := g32rep_eval_scalar g32p_rhoDual (g32rep_rep X) X.centre hdual y
  have hPQ : P ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz1, hz2⟩
    have e1 := Module.End.mem_eigenspace_iff.mp (hPe hz1)
    have e2 := Module.End.mem_eigenspace_iff.mp (hQe hz2)
    have hz : (d - d ^ 2) • z = 0 := by rw [sub_smul, ← e1, ← e2, sub_self]
    exact (smul_eq_zero.mp hz).resolve_left
      (sub_ne_zero.mpr (g32rep_cube_root_ne_square hd))
  refine ⟨x, y, hv, hw, (Submodule.eq_of_le_of_finrank_eq (sup_le hPW hQW) ?_).symm⟩
  have hs := Submodule.finrank_sup_add_finrank_inf_eq P Q
  rw [hPQ, finrank_bot, add_zero, hP6, hQ6] at hs
  rw [hs, g32rep_projA_range_finrank]

theorem g32rep_projA_preserved_aux (X : g32p_Cover A) {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)}
    (hu : u ∈ g32c_U X) :
    ∀ z ∈ LinearMap.range ((homPullback X.projA 1).baseChange ℂ),
      u z ∈ LinearMap.range ((homPullback X.projA 1).baseChange ℂ) := by
  rw [← g32rep_projA_range_comp X]
  rintro _ ⟨z, rfl⟩
  refine ⟨u z, ?_⟩
  exact (LinearMap.congr_fun (g32rep_projA_commute X hu) z).symm

theorem g32rep_weil_eigenspace_aux (X : g32p_Cover A) :
    ∃ c : ℂ, c ^ 2 + c + 1 = 0 ∧
      A.W.Vs.map ((homPullback X.projA 1).baseChange ℂ) =
        LinearMap.range ((homPullback X.projA 1).baseChange ℂ) ⊓
          Module.End.eigenspace (g32rep_rep X X.centre) c := by
  let w := HodgeBlocks.WeilAction.omegaC (3 : ℚ)
  let c : ℂ := (w - 1) / 2
  have hw : w ^ 2 = -3 := HodgeBlocks.WeilAction.omegaC_sq (by norm_num)
  have hc : c ^ 2 + c + 1 = 0 := by
    dsimp [c]
    linear_combination hw / 4
  have hwc : 1 + 2 * c = w := by dsimp [c]; ring
  refine ⟨c, hc, ?_⟩
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨LinearMap.mem_range_self _ y, ?_⟩
    apply Module.End.mem_eigenspace_iff.mpr
    have hy' : A.W.Jc y = w • y := Module.End.mem_eigenspace_iff.mp hy
    have he := g32rep_weil_intertwine X y
    rw [hy', map_smul] at he
    have ht : (2 : ℂ) • g32rep_rep X X.centre
        ((homPullback X.projA 1).baseChange ℂ y) =
        (2 : ℂ) • (c • (homPullback X.projA 1).baseChange ℂ y) := by
      calc
        _ = w • (homPullback X.projA 1).baseChange ℂ y -
            (homPullback X.projA 1).baseChange ℂ y := by rw [eq_sub_iff_add_eq, he]; abel
        _ = _ := by
          rw [smul_smul, show 2 * c = w - 1 by dsimp [c]; ring, sub_smul, one_smul]
    exact smul_right_injective _ (by norm_num : (2 : ℂ) ≠ 0) ht
  · rintro ⟨⟨y, rfl⟩, hz⟩
    refine ⟨y, ?_, rfl⟩
    change y ∈ Module.End.eigenspace A.W.Jc w
    rw [Module.End.mem_eigenspace_iff]
    apply g32rep_projA_injective X
    rw [g32rep_weil_intertwine, Module.End.mem_eigenspace_iff.mp hz, map_smul,
      smul_smul, ← hwc, add_smul, one_smul]

theorem g32rep_restrictA_intertwine (X : g32p_Cover A)
    {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)} (hu : u ∈ g32c_U X)
    (y : ℂ ⊗[ℚ] HQ A.X 1) :
    (homPullback X.projA 1).baseChange ℂ (g32c_restrict X.inclA X.projA X.NA u y) =
      u ((homPullback X.projA 1).baseChange ℂ y) := by
  obtain ⟨z, hz⟩ := g32rep_projA_preserved_aux X hu _ (LinearMap.mem_range_self _ y)
  change (homPullback X.projA 1).baseChange ℂ
    ((X.NA : ℂ)⁻¹ • (homPullback X.inclA 1).baseChange ℂ
      (u ((homPullback X.projA 1).baseChange ℂ y))) = _
  rw [← hz, g32rep_inclA_projA_C, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 X.NA_pos.ne'), one_smul]

theorem g32rep_weil_preserved_aux (X : g32p_Cover A) {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)}
    (hu : u ∈ g32c_U X) :
    ∀ y ∈ A.W.Vs, g32c_restrict X.inclA X.projA X.NA u y ∈ A.W.Vs := by
  obtain ⟨c, hc, he⟩ := g32rep_weil_eigenspace_aux X
  intro y hy
  have hyim : (homPullback X.projA 1).baseChange ℂ y ∈
      A.W.Vs.map ((homPullback X.projA 1).baseChange ℂ) := ⟨y, hy, rfl⟩
  rw [he] at hyim
  have hz : u ((homPullback X.projA 1).baseChange ℂ y) ∈
      A.W.Vs.map ((homPullback X.projA 1).baseChange ℂ) := by
    rw [he]
    refine ⟨g32rep_projA_preserved_aux X hu _ hyim.1, ?_⟩
    apply Module.End.mem_eigenspace_iff.mpr
    have hcomm := LinearMap.congr_fun (hu.2.1 X.centre)
      ((homPullback X.projA 1).baseChange ℂ y)
    change u (g32rep_rep X X.centre _) = g32rep_rep X X.centre (u _) at hcomm
    rw [← hcomm, Module.End.mem_eigenspace_iff.mp hyim.2, map_smul]
  obtain ⟨z, hz, hez⟩ := hz
  have heq : g32c_restrict X.inclA X.projA X.NA u y = z :=
    g32rep_projA_injective X ((g32rep_restrictA_intertwine X hu y).trans hez.symm)
  rw [heq]
  exact hz

theorem g32rep_weil_finrank_aux (X : g32p_Cover A) : Module.finrank ℂ A.W.Vs = 6 := by
  letI := (finiteBetti_abelian A.X).finite 1
  have hs := Submodule.finrank_sup_add_finrank_inf_eq A.W.Vs A.W.Vsbar
  have hc := A.W.isCompl_Vs_Vsbar (by norm_num : (0 : ℚ) < 3)
  rw [hc.sup_eq_top, hc.inf_eq_bot, finrank_top, finrank_bot, add_zero,
    Module.finrank_baseChange, X.dimA, A.W.finrank_Vsbar_eq_Vs] at hs
  omega

theorem g32rep_summand_selection (X : g32p_Cover A) :
    ∃ (x : g32p_rho) (y : g32p_rhoDual), x ≠ 0 ∧ y ≠ 0 ∧
      (A.W.Vs.map ((homPullback X.projA 1).baseChange ℂ) =
        (rfd_mult g32p_rho (g32rep_rep X)).map (LinearMap.applyₗ x) ∨
       A.W.Vs.map ((homPullback X.projA 1).baseChange ℂ) =
        (rfd_mult g32p_rhoDual (g32rep_rep X)).map (LinearMap.applyₗ y)) := by
  obtain ⟨x, y, hx, hy, hr⟩ := g32rep_projA_range_aux X
  obtain ⟨c, hc, he⟩ := g32rep_weil_eigenspace_aux X
  obtain ⟨d, hd, hmat⟩ := X.centre_eq
  have hd0 : d ≠ 0 := by intro h; rw [h] at hd; norm_num at hd
  have hd3 : d * d ^ 2 = 1 := by linear_combination (d - 1) * hd
  have hdi : d⁻¹ = d ^ 2 := inv_eq_of_mul_eq_one_right hd3
  have hρ := g32rep_rho_centre X hmat
  have hdual : g32p_rhoDual.ρ X.centre = d ^ 2 • LinearMap.id := by
    exact hdi ▸ g32rep_dual_scalar g32p_rho.ρ X.centre hd0 hρ
  have hP := g32rep_eval_scalar g32p_rho (g32rep_rep X) X.centre hρ x
  have hQ := g32rep_eval_scalar g32p_rhoDual (g32rep_rep X) X.centre hdual y
  refine ⟨x, y, hx, hy, ?_⟩
  rcases g32rep_cube_roots hc hd with h | h
  · left
    rw [he, hr, h]
    exact g32rep_select_eigenspace _ _ _ (g32rep_cube_root_ne_square hd) hP hQ
  · right
    rw [he, hr, h, sup_comm]
    exact g32rep_select_eigenspace _ _ _ (g32rep_cube_root_ne_square hd).symm hQ hP

theorem g32rep_det_weil_of_image (X : g32p_Cover A) (σ : FDRep ℂ g32p_G)
    [Simple σ] (x : σ) (hx : x ≠ 0)
    (him : A.W.Vs.map ((homPullback X.projA 1).baseChange ℂ) =
      (rfd_mult σ (g32rep_rep X)).map (LinearMap.applyₗ x))
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X)
    (h : ∀ y ∈ A.W.Vs, g32c_restrict X.inclA X.projA X.NA u y ∈ A.W.Vs) :
    LinearMap.det ((g32c_restrict X.inclA X.projA X.NA u).restrict h) =
      g32c_char X σ u hu := by
  have := (torusCohomology_cupProductOf X.J).finite
  let hc := g32rep_U_le X hu
  have him' : A.W.Vs.map ((homPullback X.projA 1).baseChange ℂ) =
      LinearMap.range ((LinearMap.applyₗ x).domRestrict (rfd_mult σ (g32rep_rep X))) := by
    rw [LinearMap.range_domRestrict]
    exact him
  rw [g32rep_det_transport _ (g32rep_projA_injective X) _ _ him' _ u h
    (g32rep_eval_range_preserved σ (g32rep_rep X) x u hc)
    (g32rep_restrictA_intertwine X hu)]
  rw [g32rep_det_eval_range σ (g32rep_rep X) x hx u hc, g32rep_char_eq]

theorem g32rep_weil_sign_aux (X : g32p_Cover A) :
    ∃ ε : ℤˣ, ∀ (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X)
      (h : ∀ y ∈ A.W.Vs, g32c_restrict X.inclA X.projA X.NA u y ∈ A.W.Vs),
      LinearMap.det ((g32c_restrict X.inclA X.projA X.NA u).restrict h) =
        g32c_char X g32p_rho u hu ^ (ε : ℤ) := by
  obtain ⟨x, y, hx, hy, him⟩ := g32rep_summand_selection X
  haveI := g32p_rho_simple
  haveI := g32p_rhoDual_simple
  rcases him with him | him
  · refine ⟨1, fun u hu h => ?_⟩
    rw [g32rep_det_weil_of_image X g32p_rho x hx him u hu h]
    simp only [Units.val_one, Int.cast_one, zpow_one]
  · refine ⟨-1, fun u hu h => ?_⟩
    rw [g32rep_det_weil_of_image X g32p_rhoDual y hy him u hu h]
    have := (torusCohomology_cupProductOf X.J).finite
    obtain ⟨hnd, -, hG, hU⟩ := g32rep_form_spec X
    have hd : g32c_char X g32p_rhoDual u hu * g32c_char X g32p_rho u hu = 1 := by
      rw [g32rep_char_eq, g32rep_char_eq]
      exact rfd_det_mul_dual (g32rep_rep X) (g32rep_form X) hnd hG
        g32p_rho g32p_rhoDual g32p_rho_simple g32p_rhoDual_conjugate u _ (hU u hu)
    simpa only [Units.val_neg, Units.val_one, zpow_neg_one] using eq_inv_of_mul_eq_one_left hd

end HodgeLean.Foundations.Program
