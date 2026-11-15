import Mathlib

noncomputable section
open Set Filter Topology Polynomial Manifold
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
theorem rf7_cover_range_iff_monodromy {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] {p : E → B} (hp : IsCoveringMap p) (e : E)
    (γ : FundamentalGroup B (p e)) :
    γ ∈ (FundamentalGroup.map ⟨p, hp.continuous⟩ e).range ↔
      hp.monodromy γ.asHom ⟨e, rfl⟩ = ⟨e, rfl⟩ := by
  constructor
  · rintro ⟨δ, rfl⟩
    exact hp.monodromy_map δ.asHom
  · intro hγ
    have hend : (hp.monodromy γ.asHom ⟨e, rfl⟩).val = e := congrArg Subtype.val hγ
    let δ := (hp.liftPathQuotient γ.asHom ⟨e, rfl⟩).cast rfl hend.symm
    refine ⟨.of δ, ?_⟩
    apply CategoryTheory.End.ext
    change δ.map ⟨p, hp.continuous⟩ = γ.asHom
    dsimp only [δ]
    rw [Path.Homotopic.Quotient.map_cast, hp.map_liftPathQuotient]
    simp only [Path.Homotopic.Quotient.cast_cast, Path.Homotopic.Quotient.cast_rfl_rfl]

set_option backward.isDefEq.respectTransparency false in
theorem rf7_cover_monodromy_transitive {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] [PathConnectedSpace E] {p : E → B} (hp : IsCoveringMap p) (x : B) :
    letI := hp.fundamentalGroupMulAction x
    MulAction.IsPretransitive (FundamentalGroup B x) (p ⁻¹' {x}) := by
  letI := hp.fundamentalGroupMulAction x
  constructor
  intro a b
  let δ := Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath a.val b.val)
  let γ : FundamentalGroup B x := .of ((δ.map ⟨p, hp.continuous⟩).cast a.2.symm b.2.symm)
  refine ⟨γ, ?_⟩
  exact hp.monodromy_eq_of_map_eq δ (by simp [γ])

set_option backward.isDefEq.respectTransparency false in
theorem rf7_cover_range_index {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace E] {p : E → B} (hp : IsCoveringMap p) (e : E) :
    (FundamentalGroup.map ⟨p, hp.continuous⟩ e).range.index = Nat.card (p ⁻¹' {p e}) := by
  letI := hp.fundamentalGroupMulAction (p e)
  letI := rf7_cover_monodromy_transitive hp (p e)
  have hh : (FundamentalGroup.map ⟨p, hp.continuous⟩ e).range =
      MulAction.stabilizer (FundamentalGroup B (p e)) (⟨e, rfl⟩ : p ⁻¹' {p e}) := by
    ext γ
    exact rf7_cover_range_iff_monodromy hp e γ
  exact (congrArg Subgroup.index hh).trans
    (MulAction.index_stabilizer_of_transitive (X := p ⁻¹' {p e})
      (FundamentalGroup B (p e)) (⟨e, rfl⟩ : p ⁻¹' {p e}))

set_option backward.isDefEq.respectTransparency false in
theorem rf7_cover_rangeOfEq_index {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace E] {p : E → B} (hp : IsCoveringMap p) (e : E)
    (b : B) (he : p e = b) :
    (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he).range.index = Nat.card (p ⁻¹' {b}) := by
  cases he
  have hh : FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ (rfl : p e = p e) =
      FundamentalGroup.map ⟨p, hp.continuous⟩ e := by
    apply MonoidHom.ext
    intro γ
    exact CategoryTheory.Iso.refl_conj _
  rw [hh]
  exact rf7_cover_range_index hp e

set_option backward.isDefEq.respectTransparency false in
theorem rf7_cover_lift_of_cyclic {E F B : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [TopologicalSpace B] [PathConnectedSpace E] [PathConnectedSpace F]
    [LocallyPathConnectedSpace E] {p : E → B} {q : F → B}
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) (e : E) (f : F) (he : q f = p e)
    [IsCyclic (FundamentalGroup B (p e))]
    (hcard : Nat.card (p ⁻¹' {p e}) = Nat.card (q ⁻¹' {p e})) :
    ∃ L : C(E, F), L e = f ∧ q ∘ L = p := by
  have hi : (FundamentalGroup.map ⟨p, hp.continuous⟩ e).range.index =
      (FundamentalGroup.mapOfEq ⟨q, hq.continuous⟩ he).range.index := by
    rw [rf7_cover_range_index hp e, rf7_cover_rangeOfEq_index hq f (p e) he]
    exact hcard
  have hr := IsCyclic.subgroup_eq_iff_index_eq.mpr hi
  obtain ⟨L, hL, _⟩ := hq.existsUnique_continuousMap_lifts_of_range_le
    (f := ⟨p, hp.continuous⟩) he hr.le
  exact ⟨L, hL⟩

set_option backward.isDefEq.respectTransparency false in
theorem rf7_cover_homeomorph_of_cyclic {E F B : Type*} [TopologicalSpace E]
    [TopologicalSpace F] [TopologicalSpace B] [PathConnectedSpace E] [PathConnectedSpace F]
    [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace F]
    {p : E → B} {q : F → B} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (e : E) (f : F) (he : q f = p e) [IsCyclic (FundamentalGroup B (p e))]
    (hcard : Nat.card (p ⁻¹' {p e}) = Nat.card (q ⁻¹' {p e})) :
    ∃ L : E ≃ₜ F, L e = f ∧ q ∘ L = p := by
  obtain ⟨L, hLe, hL⟩ := rf7_cover_lift_of_cyclic hp hq e f he hcard
  haveI : IsCyclic (FundamentalGroup B (q f)) := by rw [he]; infer_instance
  have hcard' : Nat.card (q ⁻¹' {q f}) = Nat.card (p ⁻¹' {q f}) := by
    rw [he]
    exact hcard.symm
  obtain ⟨R, hRf, hR⟩ := rf7_cover_lift_of_cyclic hq hp f e he.symm hcard'
  have hRL : R ∘ L = id := hp.eq_of_comp_eq (R.continuous.comp L.continuous)
    continuous_id (by funext x; exact (congrFun hR (L x)).trans (congrFun hL x))
    e (by simp only [Function.comp_apply, hLe, hRf, id_eq])
  have hLR : L ∘ R = id := hq.eq_of_comp_eq (L.continuous.comp R.continuous)
    continuous_id (by funext x; exact (congrFun hL (R x)).trans (congrFun hR x))
    f (by simp only [Function.comp_apply, hRf, hLe, id_eq])
  let H : E ≃ₜ F :=
    { toFun := L
      invFun := R
      left_inv := congrFun hRL
      right_inv := congrFun hLR
      continuous_toFun := L.continuous
      continuous_invFun := R.continuous }
  exact ⟨H, hLe, hL⟩

set_option backward.isDefEq.respectTransparency false in
theorem rf7_homeomorph_pi1_cyclic {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (h : E ≃ₜ F) (x : E) [IsCyclic (FundamentalGroup E x)] :
    IsCyclic (FundamentalGroup F (h x)) := by
  apply isCyclic_of_surjective (FundamentalGroup.map ⟨h, h.continuous⟩ x)
  intro γ
  obtain ⟨γ', hγ'⟩ := Path.Homotopic.Quotient.mk_surjective γ.asHom
  let δ : Path x x := (γ'.map h.symm.continuous).cast
    (h.symm_apply_apply x).symm (h.symm_apply_apply x).symm
  refine ⟨.of (.mk δ), ?_⟩
  apply CategoryTheory.End.ext
  change Path.Homotopic.Quotient.mk (δ.map h.continuous) = γ.asHom
  rw [← hγ']
  congr 1
  ext t
  simp [δ]

theorem rf7_nonzero_pi1_cyclic (x : {z : ℂ // z ≠ 0}) :
    IsCyclic (FundamentalGroup {z : ℂ // z ≠ 0} x) := by
  let e : (fun z : ℂ ↦ (⟨z.exp, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) ⁻¹' {x} :=
    ⟨x.val.log, Subtype.ext (Complex.exp_log x.2)⟩
  exact ((Complex.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv e).trans
    MulOpposite.opMulEquiv.symm).isCyclic.mpr inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- Source: Mathlib's radial homeomorphism from a normed space to an open ball. -/
def rf7_puncturedDiscHomeomorph (a c : ℂ) (ρ : ℝ) (hc : ‖c - a‖ < ρ) :
    ↥(Metric.ball a ρ \ {c}) ≃ₜ {z : ℂ // z ≠ 0} := by
  have hρ : 0 < ρ := (norm_nonneg _).trans_lt hc
  let e₀ : ℂ ≃ₜ Metric.ball a ρ :=
    (((Homeomorph.Set.univ ℂ).symm.trans
      (Homeomorph.setCongr (OpenPartialHomeomorph.univBall_source a ρ).symm)).trans
      (OpenPartialHomeomorph.univBall a ρ).toHomeomorphSourceTarget).trans
      (Homeomorph.setCongr (OpenPartialHomeomorph.univBall_target a hρ))
  let c' : Metric.ball a ρ := ⟨c, by simpa [Metric.mem_ball, dist_eq_norm] using hc⟩
  let e : ℂ ≃ₜ Metric.ball a ρ := (Homeomorph.addRight (e₀.symm c')).trans e₀
  have he0 : (e 0 : ℂ) = c := by simp [e, c']
  refine
    { toFun := fun z ↦ ⟨e.symm ⟨z, z.2.1⟩, ?_⟩
      invFun := fun z ↦ ⟨e z, (e z).2, ?_⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro hh
    have hh' := congrArg (fun z ↦ (e z : ℂ)) hh
    exact z.2.2 (by simpa only [e.apply_symm_apply, he0, Set.mem_singleton_iff] using hh')
  · change (e z : ℂ) ≠ c
    intro hh
    have hh' : e z = e 0 := Subtype.ext (hh.trans he0.symm)
    exact z.2 (e.injective hh')
  · intro z
    apply Subtype.ext
    exact congrArg (fun b : Metric.ball a ρ ↦ (b : ℂ)) (e.apply_symm_apply ⟨z.val, z.2.1⟩)
  · intro z
    apply Subtype.ext
    exact e.symm_apply_apply z
  · exact (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _
  · exact (continuous_subtype_val.comp (e.continuous.comp continuous_subtype_val)).subtype_mk _

theorem rf7_puncturedDisc_pi1_cyclic (a c : ℂ) (ρ : ℝ) (hc : ‖c - a‖ < ρ)
    (x : ↥(Metric.ball a ρ \ {c})) :
    IsCyclic (FundamentalGroup ↥(Metric.ball a ρ \ {c}) x) := by
  let h := rf7_puncturedDiscHomeomorph a c ρ hc
  letI := rf7_nonzero_pi1_cyclic (h x)
  have hh := rf7_homeomorph_pi1_cyclic h.symm (h x)
  exact (h.symm_apply_apply x) ▸ hh

set_option backward.isDefEq.respectTransparency false in
theorem rf7_power_fibre_card (k : ℕ) (hk : 0 < k) (a : ℂ) (ha : a ≠ 0) :
    Nat.card {w : ℂ // w ^ k = a} = k := by
  classical
  let p : ℂ[X] := Polynomial.X ^ k - Polynomial.C a
  have hp : p ≠ 0 := (Polynomial.monic_X_pow_sub_C a hk.ne').ne_zero
  have hs : p.rootSet ℂ = {w : ℂ | w ^ k = a} := by
    ext w
    simp [Polynomial.mem_rootSet, hp, p, sub_eq_zero]
  have hh := Polynomial.card_rootSet_eq_natDegree
    (K := ℂ) (Polynomial.separable_X_pow_sub_C a (Nat.cast_ne_zero.mpr hk.ne') ha)
    (IsAlgClosed.splits_domain p)
  rw [← Nat.card_eq_fintype_card] at hh
  rw [hs] at hh
  convert! hh using 1
  simp only [p, Polynomial.natDegree_X_pow_sub_C]

set_option backward.isDefEq.respectTransparency false in
theorem rf7_restrict_fibre_card {E B : Type*} (p : E → B) (S : Set B) (b : S) :
    Nat.card ((S.restrictPreimage p) ⁻¹' {b}) = Nat.card (p ⁻¹' {b.val}) := by
  apply Nat.card_congr
  refine
    { toFun := fun x ↦ ⟨x.val.val, congrArg Subtype.val x.2⟩
      invFun := fun x ↦ ⟨⟨x.val, by change p x.val ∈ S; rw [x.2]; exact b.2⟩, Subtype.ext x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

set_option backward.isDefEq.respectTransparency false in
theorem rf7_cover_codRestrict {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B) (S : Set B) (hp : IsCoveringMapOn p S) (hr : ∀ e, p e ∈ S) :
    IsCoveringMap (fun e ↦ (⟨p e, hr e⟩ : S)) := by
  let h : E ≃ₜ p ⁻¹' S :=
    { toFun := fun e ↦ ⟨e, hr e⟩
      invFun := Subtype.val
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := continuous_id.subtype_mk _
      continuous_invFun := continuous_subtype_val }
  exact hp.isCoveringMap_restrictPreimage.comp_homeomorph h

set_option backward.isDefEq.respectTransparency false in
theorem rf7_codRestrict_fibre_card {E B : Type*} (p : E → B) (S : Set B)
    (hr : ∀ e, p e ∈ S) (b : S) :
    Nat.card ((fun e ↦ (⟨p e, hr e⟩ : S)) ⁻¹' {b}) = Nat.card (p ⁻¹' {b.val}) := by
  apply Nat.card_congr
  refine
    { toFun := fun x ↦ ⟨x.val, congrArg Subtype.val x.2⟩
      invFun := fun x ↦ ⟨x.val, Subtype.ext x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

set_option backward.isDefEq.respectTransparency false in
theorem rf7_mdifferentiable_root {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (n : ℕ) (hn : 0 < n) (w : Y → ℂ) (hw : Continuous w) (h0 : ∀ y, w y ≠ 0)
    (hpw : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun y ↦ w y ^ n)) :
    MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) w := by
  intro y
  have hp : HasStrictDerivAt (fun z : ℂ ↦ z ^ n) ((n : ℂ) * w y ^ (n - 1)) (w y) := by
    convert! (hasStrictDerivAt_id (w y)).pow n using 1 <;> simp
  have hd : (n : ℂ) * w y ^ (n - 1) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') (pow_ne_zero _ (h0 y))
  have heq := hw.continuousAt.eventually (hp.eventually_left_inverse hd)
  exact (((hp.to_localInverse hd).hasDerivAt.differentiableAt.mdifferentiableAt).comp y
    (hpw y)).congr_of_eventuallyEq (Filter.EventuallyEq.symm heq)

theorem rf7_shifted_power_card (c : ℂ) (k : ℕ) (hk : 0 < k) (z : ℂ) (hz : z ≠ c) :
    Nat.card ((fun w : ℂ ↦ c + w ^ k) ⁻¹' {z}) = k := by
  have hset : ((fun w : ℂ ↦ c + w ^ k) ⁻¹' {z}) = {w : ℂ | w ^ k = z - c} := by
    ext w
    change c + w ^ k = z ↔ w ^ k = z - c
    constructor <;> intro h <;> linear_combination h
  rw [hset]
  exact rf7_power_fibre_card k hk (z - c) (sub_ne_zero.mpr hz)


theorem rf7_puncturedDisc_pathConnected (a c : ℂ) (ρ : ℝ) (hc : ‖c - a‖ < ρ) :
    PathConnectedSpace ↥(Metric.ball a ρ \ {c}) := by
  have hN : IsPathConnected ({(0 : ℂ)}ᶜ) :=
    isPathConnected_compl_singleton_of_one_lt_rank (by simp) 0
  have hset : ({(0 : ℂ)}ᶜ : Set ℂ) = {z : ℂ | z ≠ 0} := by ext z; simp
  rw [hset] at hN
  letI : PathConnectedSpace {z : ℂ // z ≠ 0} := isPathConnected_iff_pathConnectedSpace.mp hN
  exact (rf7_puncturedDiscHomeomorph a c ρ hc).symm.pathConnectedSpace

theorem rf7_star_punctured_pathConnected (W : Set ℂ) (ho : IsOpen W)
    (h0 : (0 : ℂ) ∈ W) (hs : StarConvex ℝ (0 : ℂ) W) :
    IsPathConnected (W \ {0}) := by
  obtain ⟨δ, hδ, hδW⟩ := Metric.isOpen_iff.mp ho 0 h0
  let B := Metric.ball (0 : ℂ) δ \ {0}
  have hB : IsPathConnected B := by
    apply isPathConnected_iff_pathConnectedSpace.mpr
    exact rf7_puncturedDisc_pathConnected 0 0 δ (by simpa using hδ)
  have hBW : B ⊆ W \ {0} := fun z hz ↦ ⟨hδW hz.1, hz.2⟩
  have hstep (w : ℂ) (hw : w ∈ W \ {0}) :
      ∃ u ∈ B, JoinedIn (W \ {0}) u w := by
    have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw.2
    let s : ℝ := δ / (2 * (δ + ‖w‖))
    have hd : 0 < 2 * (δ + ‖w‖) := by positivity
    have hs0 : 0 < s := div_pos hδ hd
    have hs1 : s < 1 := (div_lt_one hd).mpr (by linarith)
    have hsn : s * ‖w‖ < δ := by
      dsimp [s]
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ hd).mpr
      nlinarith
    refine ⟨s • w, ⟨?_, ?_⟩, JoinedIn.of_segment_subset ?_⟩
    · simpa only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hs0.le] using hsn
    · exact smul_ne_zero hs0.ne' hw.2
    · rintro z ⟨α, β, hα, hβ, hαβ, rfl⟩
      have hc0 : 0 < α * s + β := by
        by_cases hα0 : α = 0
        · simp only [hα0, zero_add] at hαβ
          simp [hα0, hαβ]
        · have hαp : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
          positivity
      have hc1 : α * s + β ≤ 1 := by nlinarith
      have heq : α • s • w + β • w = (α * s + β) • w := by rw [smul_smul, add_smul]
      rw [heq]
      refine ⟨?_, smul_ne_zero hc0.ne' hw.2⟩
      have hh := hs hw.1 (sub_nonneg.mpr hc1) hc0.le (sub_add_cancel 1 (α * s + β))
      simpa only [smul_zero, zero_add] using hh
  obtain ⟨u₀, hu₀⟩ := hB.nonempty
  refine ⟨u₀, hBW hu₀, ?_⟩
  intro w hw
  obtain ⟨u, hu, hpath⟩ := hstep w hw
  exact ((hB.joinedIn u₀ hu₀ u hu).mono hBW).trans hpath

theorem rf7_power_domain_star (a c : ℂ) (ρ : ℝ) (hc : ‖c - a‖ < ρ) (k : ℕ) :
    StarConvex ℝ (0 : ℂ) {w : ℂ | ‖c + w ^ k - a‖ < ρ} := by
  intro w hw α β hα hβ hαβ
  simp only [smul_zero, zero_add, Set.mem_setOf_eq] at hw ⊢
  have hβ1 : β ≤ 1 := by linarith
  have ht0 : 0 ≤ β ^ k := pow_nonneg hβ _
  have ht1 : β ^ k ≤ 1 := pow_le_one₀ hβ hβ1
  have hh := (convex_ball a ρ)
    (show c ∈ Metric.ball a ρ by simpa [Metric.mem_ball, dist_eq_norm] using hc)
    (show c + w ^ k ∈ Metric.ball a ρ by simpa [Metric.mem_ball, dist_eq_norm] using hw)
    (sub_nonneg.mpr ht1) ht0 (sub_add_cancel 1 (β ^ k))
  have heq : (1 - β ^ k) • c + β ^ k • (c + w ^ k) = c + (β • w) ^ k := by
    simp only [Complex.real_smul, mul_pow, Complex.ofReal_pow, Complex.ofReal_sub,
      Complex.ofReal_one]
    ring
  rw [heq] at hh
  simpa [Metric.mem_ball, dist_eq_norm] using hh

set_option backward.isDefEq.respectTransparency false in
theorem rf7_offcentre_topological {Y : Type*} [TopologicalSpace Y]
    [PathConnectedSpace Y] [LocallyPathConnectedSpace Y]
    (a c : ℂ) (ρ : ℝ) (hc : ‖c - a‖ < ρ) (k : ℕ) (hk : 0 < k)
    (q : Y → ℂ) (hrange : ∀ y, q y ∈ Metric.ball a ρ \ {c})
    (hcov : IsCoveringMapOn q (Metric.ball a ρ \ {c}))
    (hdeg : ∀ z ∈ Metric.ball a ρ \ {c}, Nat.card (q ⁻¹' {z}) = k) :
    ∃ v : Y → ℂ, IsOpenEmbedding v ∧ Function.Injective v ∧
      range v = {w : ℂ | w ≠ 0 ∧ ‖c + w ^ k - a‖ < ρ} ∧ ∀ y, q y = c + v y ^ k := by
  classical
  let S := Metric.ball a ρ \ {c}
  let f : ℂ → ℂ := fun w ↦ c + w ^ k
  let U := f ⁻¹' S
  let p : Y → S := fun y ↦ ⟨q y, hrange y⟩
  let r : U → S := S.restrictPreimage f
  have hp : IsCoveringMap p := rf7_cover_codRestrict q S hcov hrange
  have hf : IsCoveringMapOn f S := by
    have hh := (isCoveringMapOn_npow (𝕜 := ℂ) k (Nat.cast_ne_zero.mpr hk.ne')).homeomorph_comp
      (Homeomorph.addLeft c)
    apply hh.mono
    intro z hz
    change -c + z ≠ 0
    intro hh
    apply hz.2
    change z = c
    linear_combination hh
  have hr : IsCoveringMap r := hf.isCoveringMap_restrictPreimage
  have hS : IsOpen S := Metric.isOpen_ball.sdiff isClosed_singleton
  have hU : IsOpen U := hS.preimage (continuous_const.add (continuous_pow k))
  letI : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace
  let W : Set ℂ := {w | ‖c + w ^ k - a‖ < ρ}
  have hW : IsOpen W := isOpen_lt (by fun_prop) continuous_const
  have hW0 : (0 : ℂ) ∈ W := by simpa [W, zero_pow hk.ne'] using hc
  have hset : U = W \ {0} := by
    ext w
    simp only [U, f, S, W, Set.mem_preimage, Set.mem_sdiff, Metric.mem_ball,
      dist_eq_norm, Set.mem_setOf_eq, Set.mem_singleton_iff]
    simp only [add_eq_left, pow_eq_zero_iff hk.ne']
  letI : PathConnectedSpace U := by
    rw [hset]
    exact isPathConnected_iff_pathConnectedSpace.mp
      (rf7_star_punctured_pathConnected W hW hW0 (rf7_power_domain_star a c ρ hc k))
  have hpCard (z : S) : Nat.card (p ⁻¹' {z}) = k :=
    (rf7_codRestrict_fibre_card q S hrange z).trans (hdeg z z.2)
  have hrCard (z : S) : Nat.card (r ⁻¹' {z}) = k :=
    (rf7_restrict_fibre_card f S z).trans
      (rf7_shifted_power_card c k hk z (by simpa only [Set.mem_singleton_iff] using z.2.2))
  let y₀ : Y := Classical.arbitrary Y
  have hpos : 0 < Nat.card (r ⁻¹' {p y₀}) := by rw [hrCard]; exact hk
  obtain ⟨u₀, hu₀⟩ := (Nat.card_pos_iff.mp hpos).1
  letI := rf7_puncturedDisc_pi1_cyclic a c ρ hc (p y₀)
  obtain ⟨L, _, hL⟩ := rf7_cover_homeomorph_of_cyclic hp hr y₀ u₀ hu₀
    ((hpCard (p y₀)).trans (hrCard (p y₀)).symm)
  let v : Y → ℂ := fun y ↦ L y
  have hmem (w : ℂ) : w ∈ U ↔ w ≠ 0 ∧ ‖c + w ^ k - a‖ < ρ := by
    rw [hset]
    exact and_comm
  refine ⟨v, hU.isOpenEmbedding_subtypeVal.comp L.isOpenEmbedding,
    Subtype.val_injective.comp L.injective, ?_, ?_⟩
  · ext w
    constructor
    · rintro ⟨y, rfl⟩
      exact (hmem _).mp (L y).2
    · intro hw
      obtain ⟨y, hy⟩ := L.surjective ⟨w, (hmem w).mpr hw⟩
      exact ⟨y, congrArg Subtype.val hy⟩
  · intro y
    exact (congrArg (fun z : S ↦ z.val) (congrFun hL y)).symm


theorem rf7_component_image_eq {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    [LocallyConnectedSpace X] (f : X → Z) (hf : Continuous f) (ho : IsOpenMap f)
    (hc : IsClosedMap f) (S : Set Z) (hS : IsOpen S) (hconn : IsConnected S)
    (x : X) (hx : f x ∈ S) : f '' connectedComponentIn (f ⁻¹' S) x = S := by
  let U := f ⁻¹' S
  let x' : U := ⟨x, hx⟩
  let F : U → S := S.restrictPreimage f
  letI : LocallyConnectedSpace U := (hS.preimage hf).locallyConnectedSpace
  letI : ConnectedSpace S := isConnected_iff_connectedSpace.mp hconn
  have hclosed : IsClosed (F '' connectedComponent x') :=
    hc.restrictPreimage S _ isClosed_connectedComponent
  have hopen : IsOpen (F '' connectedComponent x') :=
    ho.restrictPreimage S _ isOpen_connectedComponent
  have hne : (F '' connectedComponent x').Nonempty :=
    ⟨F x', x', mem_connectedComponent, rfl⟩
  have hall := (show IsClopen (F '' connectedComponent x') from ⟨hclosed, hopen⟩).eq_univ hne
  rw [connectedComponentIn_eq_image (show x ∈ f ⁻¹' S from hx)]
  apply Set.Subset.antisymm
  · rintro z ⟨y, ⟨u, hu, rfl⟩, rfl⟩
    exact u.2
  · intro z hz
    have hm : (⟨z, hz⟩ : S) ∈ F '' connectedComponent x' := hall ▸ Set.mem_univ _
    obtain ⟨u, hu, heq⟩ := hm
    exact ⟨u, ⟨u, hu, rfl⟩, congrArg Subtype.val heq⟩

theorem rf7_component_compact_inter {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    (f : X → Z) (S K : Set Z) (hK : IsCompact (f ⁻¹' K)) (hKS : K ⊆ S)
    (x : X) (hx : f x ∈ S) :
    IsCompact (connectedComponentIn (f ⁻¹' S) x ∩ f ⁻¹' K) := by
  let U := f ⁻¹' S
  let x' : U := ⟨x, hx⟩
  have hKU : f ⁻¹' K ⊆ Set.range (Subtype.val : U → X) := by
    intro y hy
    exact ⟨⟨y, hKS hy⟩, rfl⟩
  have hK' : IsCompact ((Subtype.val : U → X) ⁻¹' (f ⁻¹' K)) :=
    IsInducing.subtypeVal.isCompact_preimage' hK hKU
  have hh := (hK'.inter_left (isClosed_connectedComponent (x := x'))).image continuous_subtype_val
  convert hh using 1
  rw [connectedComponentIn_eq_image (show x ∈ f ⁻¹' S from hx), Set.image_inter Subtype.val_injective,
    Set.image_preimage_eq_of_subset hKU]


theorem rf7_continuousAt_zero_of_pow {X : Type*} [TopologicalSpace X]
    (f : X → ℂ) (n : ℕ) (hn : 0 < n) (x : X) (hf : f x = 0)
    (hp : ContinuousAt (fun y ↦ f y ^ n) x) : ContinuousAt f x := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hh := Metric.tendsto_nhds.mp hp (ε ^ n) (pow_pos hε n)
  filter_upwards [hh] with y hy
  rw [hf, zero_pow hn.ne', dist_zero_right, norm_pow] at hy
  rw [hf, dist_zero_right]
  by_contra! h
  have hh := pow_le_pow_left₀ hε.le h n
  exact (not_lt_of_ge hh) hy

theorem rf7_zero_fibre_of_inverse_limit {X Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Z] [T2Space Z] (a : X → Z) (ha : Continuous a)
    (w : X → ℂ) (hw : Continuous w) (hdense : Dense {x | w x ≠ 0})
    (j : ℂ → Z) (z₀ : Z) (hj : Tendsto j (𝓝[≠] (0 : ℂ)) (𝓝 z₀))
    (hinv : ∀ x, w x ≠ 0 → j (w x) = a x) (x : X) (hx : w x = 0) : a x = z₀ := by
  let F := 𝓝[{x | w x ≠ 0}] x
  haveI : F.NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hdense x)
  have htw : Tendsto w F (𝓝 (0 : ℂ)) := by
    simpa only [hx] using
      (hw.continuousAt.tendsto.mono_left (show F ≤ 𝓝 x from nhdsWithin_le_nhds))
  have htw' : Tendsto w F (𝓝[≠] (0 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨htw, self_mem_nhdsWithin⟩
  have heq : j ∘ w =ᶠ[F] a := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hinv y hy
  have htj : Tendsto a F (𝓝 z₀) := (hj.comp htw').congr' heq
  exact tendsto_nhds_unique
    (ha.continuousAt.tendsto.mono_left (show F ≤ 𝓝 x from nhdsWithin_le_nhds)) htj


theorem rf7_covering_on_component {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    [T2Space X] [LocallyConnectedSpace X] (f : X → Z) (hf : Continuous f)
    (hc : IsClosedMap f) (hfin : ∀ z, (f ⁻¹' {z}).Finite)
    (S T : Set Z) (hS : IsOpen S) (hcov : IsCoveringMapOn f T)
    (x : X) (hx : f x ∈ S) :
    let U := f ⁻¹' S
    let x' : U := ⟨x, hx⟩
    IsCoveringMapOn
      (fun d : connectedComponent x' ↦ S.restrictPreimage f d.val)
      (Subtype.val ⁻¹' T) := by
  let U := f ⁻¹' S
  let x' : U := ⟨x, hx⟩
  let D := connectedComponent x'
  let F : U → S := S.restrictPreimage f
  let Q : D → S := fun d ↦ F d.val
  let a : D → X := fun d ↦ d.val.val
  letI : LocallyConnectedSpace U := (hS.preimage hf).locallyConnectedSpace
  have hdopen : IsOpen D := isOpen_connectedComponent
  have hdclosed : IsClosed D := isClosed_connectedComponent
  have hclosed : IsClosedMap Q :=
    (hc.restrictPreimage S).comp hdclosed.isClosedEmbedding_subtypeVal.isClosedMap
  have hfinite (z : S) : (Q ⁻¹' {z}).Finite := by
    have ha : Function.Injective a := Subtype.val_injective.comp Subtype.val_injective
    have hh := Set.Finite.preimage ha.injOn (hfin z.val)
    have heq : a ⁻¹' (f ⁻¹' {z.val}) = Q ⁻¹' {z} := by
      ext d
      change f d.val.val = z.val ↔ Q d = z
      exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
    rw [← heq]
    exact hh
  have hloc : IsLocalHomeomorphOn Q (Q ⁻¹' (Subtype.val ⁻¹' T)) := by
    have hF := (hcov.restrictPreimage S).isLocalHomeomorphOn
    have hinc : IsLocalHomeomorphOn (Subtype.val : D → U)
        (Q ⁻¹' (Subtype.val ⁻¹' T)) :=
      hdopen.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
    exact hF.comp hinc (fun d hd ↦ hd)
  exact hclosed.isCoveringMapOn_of_isLocalHomeomorphOn (fun z _ ↦ hfinite z) hloc


theorem rf7_covering_comp_subtype {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (S T : Set Z) (hT : IsOpen T) (hTS : T ⊆ S) (q : Y → S) (hq : Continuous q)
    (hcov : IsCoveringMapOn q ((Subtype.val : S → Z) ⁻¹' T)) :
    IsCoveringMapOn (fun y ↦ (q y).val) T := by
  let e : ((Subtype.val : S → Z) ⁻¹' T) ≃ₜ T :=
    IsEmbedding.subtypeVal.homeomorphOfSubsetRange (fun z hz ↦ ⟨⟨z, hTS hz⟩, rfl⟩)
  have hh := hcov.isCoveringMap_restrictPreimage.homeomorph_comp e
  exact IsCoveringMapOn.of_isCoveringMap_restrictPreimage T hT
    (hT.preimage (continuous_subtype_val.comp hq)) hh

end HodgeLean.Foundations.Program
