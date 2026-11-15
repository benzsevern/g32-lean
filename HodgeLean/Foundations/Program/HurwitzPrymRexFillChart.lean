import HodgeLean.Foundations.Program.HurwitzPrymRexFill

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-rex`: the filled surface and its charts

The filled surface is `C = U ⊕ Σ_b G ⧸ ⟨h_b⟩`: one new point for each coset of the deck generator
over each puncture. At a point of `U` the chart is the chart of `Y` read through a local inverse
of `p`; at a new point `(b, q)` the chart is `0` at the point and `v` at `M_{q.out} v`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Topology Metric Set Complex HodgeLean.Foundations.Program.HurwitzPrymRexPunct

namespace HodgeLean.Foundations.Program

namespace HurwitzPrymRexFill

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y]
variable {B : Set Y} {G U : Type} [Group G] [TopologicalSpace U] [MulAction G U]
variable {p : U → {y : Y // y ∉ B}}

variable (E') in
/-- **The choices behind the filling**: a coordinate identification `κ' : E' ≃ ℂ`, radii of
pairwise disjoint coordinate discs meeting `B` only at their centres, and a base point of `U`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, Theorem 8.4. -/
structure Setup (p : U → {y : Y // y ∉ B}) where
  κ' : E' ≃L[ℂ] ℂ
  r : B → ℝ
  hr : ∀ b, 0 < r b
  hTgt : ∀ b, ball (0 : ℂ) (r b) ⊆ Tgt κ' b.1
  havoid : ∀ b, ∀ z ∈ ball (0 : ℂ) (r b), ξY κ' b.1 z ∈ B → z = 0
  hdisj : ∀ b b', b ≠ b' → ∀ z ∈ ball (0 : ℂ) (r b), ∀ z' ∈ ball (0 : ℂ) (r b'),
    ξY κ' b.1 z ≠ ξY κ' b'.1 z'
  u₀ : U
  hBc : IsClosed B

namespace Setup

variable (S : Setup E' p) (hp : IsQuotientCoveringMap p G)

/-- The puncture datum at `b`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, Theorem 8.4 (filling the punctures). -/
def D (b : B) : Datum p G :=
  mkDatum hp S.κ' b.1 (S.r b) (S.hr b) (S.hTgt b) (S.havoid b) S.u₀

example (b : B) : (S.D hp b).r = S.r b := rfl

/-- **The new points**: over each puncture `b`, the cosets of the deck generator `h_b`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, Theorem 8.4 (filling the punctures). -/
abbrev Punct : Type := Σ b : B, G ⧸ Subgroup.zpowers (S.D hp b).h

/-- **The filled surface** `C = U ⊕ Σ_b G ⧸ ⟨h_b⟩`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, Theorem 8.4 (filling the punctures). -/
abbrev C : Type := U ⊕ S.Punct hp

example (u : U) : S.C hp := Sum.inl u

example (b : B) (q : G ⧸ Subgroup.zpowers (S.D hp b).h) : S.Punct hp := ⟨b, q⟩

end Setup

/-! ## Charts -/

/-- Push a chart on `U` to `U ⊕ P` along `inl`.
Source: Mathlib `OpenPartialHomeomorph.lift_openEmbedding` (the same construction for `PartialEquiv`). -/
def liftL {P : Type} (e : PartialEquiv U ℂ) : PartialEquiv (U ⊕ P) ℂ where
  toFun := Sum.elim e (fun _ ↦ 0)
  invFun := Sum.inl ∘ e.symm
  source := Sum.inl '' e.source
  target := e.target
  map_source' := by
    rintro _ ⟨u, hu, rfl⟩
    exact e.map_source hu
  map_target' := fun z hz ↦ ⟨_, e.map_target hz, rfl⟩
  left_inv' := by
    rintro _ ⟨u, hu, rfl⟩
    simp [e.left_inv hu]
  right_inv' := fun z hz ↦ by simp [e.right_inv hz]

example {P : Type} (e : PartialEquiv U ℂ) (u : U) : liftL (P := P) e (Sum.inl u) = e u := rfl

omit [TopologicalSpace U] in
theorem liftL_symm_trans {P : Type} (e e' : PartialEquiv U ℂ) :
    (liftL (P := P) e).symm.trans (liftL e') = e.symm.trans e' := by
  apply PartialEquiv.ext
  · intro z; rfl
  · intro z; rfl
  · ext z
    change z ∈ e.target ∧ Sum.inl (e.symm z) ∈ Sum.inl '' e'.source ↔
      z ∈ e.target ∧ e.symm z ∈ e'.source
    rw [Sum.inl_injective.mem_set_image]

namespace Setup

variable (S : Setup E' p) (hp : IsQuotientCoveringMap p G) [Finite G]

/-- **The chart at a new point** `(b, q)`: `0` at the point, `v` at `M_{q.out} v`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, Theorem 8.4 (filling the punctures). -/
def pChart (c : S.Punct hp) : PartialEquiv (S.C hp) ℂ where
  toFun x := match x with
    | Sum.inl u =>
      haveI := Classical.propDecidable (∃ v ∈ (S.D hp c.1).Dom, (S.D hp c.1).M c.2.out v = u)
      if h : ∃ v ∈ (S.D hp c.1).Dom, (S.D hp c.1).M c.2.out v = u then h.choose else 0
    | Sum.inr _ => 0
  invFun v :=
    haveI := Classical.propDecidable (v = 0)
    if v = 0 then Sum.inr c else Sum.inl ((S.D hp c.1).M c.2.out v)
  source := {Sum.inr c} ∪ Sum.inl '' ((S.D hp c.1).M c.2.out '' (S.D hp c.1).Dom)
  target := {v | ‖v‖ ^ (S.D hp c.1).e < S.r c.1}
  map_source' := by
    rintro x (hx | ⟨u, ⟨v, hv, rfl⟩, rfl⟩)
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      simp only [Set.mem_setOf_eq, norm_zero]
      rw [zero_pow (S.D hp c.1).e_pos.ne']
      exact S.hr c.1
    · have h : ∃ v' ∈ (S.D hp c.1).Dom, (S.D hp c.1).M c.2.out v' = (S.D hp c.1).M c.2.out v :=
        ⟨v, hv, rfl⟩
      simp only [dif_pos h, Set.mem_setOf_eq]
      exact h.choose_spec.1.2
  map_target' := by
    intro v hv
    by_cases h0 : v = 0
    · simp [h0]
    · simp only [if_neg h0]
      exact Or.inr ⟨_, ⟨v, ⟨h0, hv⟩, rfl⟩, rfl⟩
  left_inv' := by
    rintro x (hx | ⟨u, ⟨v, hv, rfl⟩, rfl⟩)
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      simp
    · have h : ∃ v' ∈ (S.D hp c.1).Dom, (S.D hp c.1).M c.2.out v' = (S.D hp c.1).M c.2.out v :=
        ⟨v, hv, rfl⟩
      simp only [dif_pos h, if_neg h.choose_spec.1.1]
      rw [h.choose_spec.2]
  right_inv' := by
    intro v hv
    by_cases h0 : v = 0
    · simp [h0]
    · have hvD : v ∈ (S.D hp c.1).Dom := ⟨h0, hv⟩
      have h : ∃ v' ∈ (S.D hp c.1).Dom, (S.D hp c.1).M c.2.out v' = (S.D hp c.1).M c.2.out v :=
        ⟨v, hvD, rfl⟩
      simp only [if_neg h0, dif_pos h]
      exact Datum.M_injOn hp _ h.choose_spec.1 hvD h.choose_spec.2

end Setup

namespace Setup

variable (S : Setup E' p) (hp : IsQuotientCoveringMap p G) [Finite G]

omit [TopologicalSpace U] in
theorem isOpenEmbedding_val (hBc : IsClosed B) :
    IsOpenEmbedding (Subtype.val : {y : Y // y ∉ B} → Y) :=
  ⟨⟨isInducing_val B, Subtype.val_injective⟩, by
    rw [Subtype.range_val_subtype]
    exact hBc.isOpen_compl⟩

/-- The inclusion `Y ∖ B → Y` as a partial homeomorphism.
Source: Mathlib `IsOpenEmbedding.toOpenPartialHomeomorph`. -/
def valHom : OpenPartialHomeomorph {y : Y // y ∉ B} Y :=
  haveI : Nonempty {y : Y // y ∉ B} := ⟨p S.u₀⟩
  (isOpenEmbedding_val S.hBc).toOpenPartialHomeomorph

theorem valHom_apply (y : {y : Y // y ∉ B}) : S.valHom y = y.1 := rfl

example (y : {y : Y // y ∉ B}) : S.valHom y = y.1 := S.valHom_apply y

omit [Finite G] in
/-- A local inverse of `p` at `u`.
Source: Mathlib `IsCoveringMap.isLocalHomeomorph` (a covering map is a local homeomorphism). -/
def σ (hp : IsQuotientCoveringMap p G) (u : U) : OpenPartialHomeomorph U {y : Y // y ∉ B} :=
  (hp.isCoveringMap.isLocalHomeomorph u).choose

omit [Finite G] in
theorem mem_σ_source (hp : IsQuotientCoveringMap p G) (u : U) : u ∈ (σ hp u).source :=
  (hp.isCoveringMap.isLocalHomeomorph u).choose_spec.1

omit [Finite G] in
example (hp : IsQuotientCoveringMap p G) (u : U) : u ∈ (σ hp u).source := mem_σ_source hp u

omit [Finite G] in
theorem σ_eq (hp : IsQuotientCoveringMap p G) (u : U) : p = σ hp u :=
  (hp.isCoveringMap.isLocalHomeomorph u).choose_spec.2

/-- **The chart of `Y` read on `U`** near `u`: `u' ↦ κ' (φ_{p u} (p u'))`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, Theorem 8.4 (filling the punctures). -/
def aU (u : U) : OpenPartialHomeomorph U ℂ :=
  (σ hp u).trans (S.valHom.trans ((chartAt E' (p u).1).trans
    S.κ'.toHomeomorph.toOpenPartialHomeomorph))

theorem aU_apply (u u' : U) : S.aU hp u u' = S.κ' (chartAt E' (p u).1 (p u').1) := by
  simp [aU, ← σ_eq hp u, valHom_apply]

theorem mem_aU_source (u : U) : u ∈ (S.aU hp u).source := by
  simp [aU, valHom, ← σ_eq hp u, mem_σ_source hp u]

example (u : U) : u ∈ (S.aU hp u).source := S.mem_aU_source hp u

/-- **The preferred chart** of the filled surface, in `ℂ`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, Theorem 8.4 (filling the punctures). -/
def chart (x : S.C hp) : PartialEquiv (S.C hp) ℂ :=
  match x with
  | Sum.inl u => liftL (S.aU hp u).toPartialEquiv
  | Sum.inr c => S.pChart hp c

example (c : S.Punct hp) : S.chart hp (Sum.inr c) = S.pChart hp c := rfl

theorem mem_chart_source (x : S.C hp) : x ∈ (S.chart hp x).source := by
  rcases x with u | c
  · exact ⟨u, S.mem_aU_source hp u, rfl⟩
  · exact Or.inl rfl

/-! ## Transition maps -/

example (c : S.Punct hp) : S.pChart hp c (Sum.inr c) = 0 := rfl

theorem val_p_M (b : B) (g : G) {v : ℂ} (hv : v ∈ (S.D hp b).Dom) :
    (p ((S.D hp b).M g v)).1 = ξY S.κ' b.1 (v ^ (S.D hp b).e) := by
  rw [Datum.p_M hp g hv]
  exact ξB_val (ξY_not_mem (S.havoid b)
    ⟨mem_ball_zero_iff.2 (by rw [norm_pow]; exact hv.2), pow_ne_zero _ hv.1⟩)

theorem pChart_inl_M (c : S.Punct hp) {v : ℂ} (hv : v ∈ (S.D hp c.1).Dom) :
    S.pChart hp c (Sum.inl ((S.D hp c.1).M c.2.out v)) = v := by
  have h := (S.pChart hp c).right_inv (x := v) hv.2
  have h0 : (S.pChart hp c).symm v = Sum.inl ((S.D hp c.1).M c.2.out v) := by
    change (if v = 0 then _ else _) = _
    rw [if_neg hv.1]
  rwa [h0] at h

theorem pChart_symm_of_ne {c : S.Punct hp} {v : ℂ} (hv : v ≠ 0) :
    (S.pChart hp c).symm v = Sum.inl ((S.D hp c.1).M c.2.out v) := by
  change (if v = 0 then _ else _) = _
  rw [if_neg hv]

theorem pChart_symm_zero (c : S.Punct hp) : (S.pChart hp c).symm 0 = Sum.inr c := by
  change (if (0 : ℂ) = 0 then _ else _) = _
  rw [if_pos rfl]

/-- **Distinct new points have disjoint chart domains.** -/
theorem pChart_source_disjoint {c c' : S.Punct hp} (hne : c ≠ c') :
    Disjoint (S.pChart hp c).source (S.pChart hp c').source := by
  rw [Set.disjoint_left]
  obtain ⟨b, q⟩ := c
  obtain ⟨b', q'⟩ := c'
  rintro x (hx | ⟨u, ⟨v, hv, rfl⟩, rfl⟩) (hx' | ⟨u', ⟨v', hv', hu'⟩, hx'⟩)
  · rw [Set.mem_singleton_iff] at hx hx'
    exact hne (Sum.inr_injective (hx.symm.trans hx'))
  · rw [Set.mem_singleton_iff] at hx
    exact Sum.inl_ne_inr (hx'.trans hx)
  · rw [Set.mem_singleton_iff] at hx'
    exact Sum.inl_ne_inr hx'
  · have hu := Sum.inl_injective hx'
    subst hu
    by_cases hb : b = b'
    · subst hb
      obtain ⟨n, hn⟩ := Datum.M_eq_M_coset hp hv' hv hu'
      apply hne
      congr 1
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
      rw [hn]
      simp [Subgroup.mem_zpowers_iff]
    · have h1 := S.val_p_M hp b q.out hv
      have h2 := S.val_p_M hp b' q'.out hv'
      rw [hu'] at h2
      refine S.hdisj b b' hb _ ?_ _ ?_ (h1.symm.trans h2)
      · exact mem_ball_zero_iff.2 (by rw [norm_pow]; exact hv.2)
      · exact mem_ball_zero_iff.2 (by rw [norm_pow]; exact hv'.2)

theorem transition_AA (u u' : U) :
    IsOpen ((S.chart hp (Sum.inl u)).symm.trans (S.chart hp (Sum.inl u'))).source ∧
      ContinuousOn ((S.chart hp (Sum.inl u)).symm.trans (S.chart hp (Sum.inl u')))
        ((S.chart hp (Sum.inl u)).symm.trans (S.chart hp (Sum.inl u'))).source := by
  simp only [chart]
  rw [liftL_symm_trans]
  exact ⟨((S.aU hp u).symm.trans (S.aU hp u')).open_source,
    ((S.aU hp u).symm.trans (S.aU hp u')).continuousOn⟩

theorem source_PA (c : S.Punct hp) (u : U) :
    ((S.chart hp (Sum.inr c)).symm.trans (S.chart hp (Sum.inl u))).source =
      (S.D hp c.1).Dom ∩ (S.D hp c.1).M c.2.out ⁻¹' (S.aU hp u).source := by
  ext v
  simp only [chart, PartialEquiv.trans_source, PartialEquiv.symm_source, mem_inter_iff,
    mem_preimage]
  constructor
  · rintro ⟨hv, hv'⟩
    by_cases h0 : v = 0
    · rw [h0, pChart_symm_zero] at hv'
      obtain ⟨_, -, h⟩ := hv'
      exact absurd h Sum.inl_ne_inr
    · rw [pChart_symm_of_ne S hp h0] at hv'
      exact ⟨⟨h0, hv⟩, (Sum.inl_injective.mem_set_image).1 hv'⟩
  · rintro ⟨hv, hv'⟩
    refine ⟨hv.2, ?_⟩
    rw [pChart_symm_of_ne S hp hv.1]
    exact ⟨_, hv', rfl⟩

theorem transition_PA (c : S.Punct hp) (u : U) :
    IsOpen ((S.chart hp (Sum.inr c)).symm.trans (S.chart hp (Sum.inl u))).source ∧
      ContinuousOn ((S.chart hp (Sum.inr c)).symm.trans (S.chart hp (Sum.inl u)))
        ((S.chart hp (Sum.inr c)).symm.trans (S.chart hp (Sum.inl u))).source := by
  rw [source_PA]
  refine ⟨(Datum.continuousOn_M hp _).isOpen_inter_preimage (S.D hp c.1).isOpen_Dom
    (S.aU hp u).open_source, ?_⟩
  have hc : ContinuousOn (fun v ↦ S.aU hp u ((S.D hp c.1).M c.2.out v))
      ((S.D hp c.1).Dom ∩ (S.D hp c.1).M c.2.out ⁻¹' (S.aU hp u).source) :=
    (S.aU hp u).continuousOn.comp ((Datum.continuousOn_M hp _).mono inter_subset_left)
      fun v hv ↦ hv.2
  refine hc.congr fun v hv ↦ ?_
  change Sum.elim (S.aU hp u) (fun _ ↦ 0) ((S.pChart hp c).symm v) = _
  rw [pChart_symm_of_ne S hp hv.1.1]
  rfl

theorem source_AP (u : U) (c : S.Punct hp) :
    ((S.chart hp (Sum.inl u)).symm.trans (S.chart hp (Sum.inr c))).source =
      (S.aU hp u).target ∩ (S.aU hp u).symm ⁻¹' ((S.D hp c.1).M c.2.out '' (S.D hp c.1).Dom) := by
  ext z
  simp only [chart, PartialEquiv.trans_source, PartialEquiv.symm_source, mem_inter_iff,
    mem_preimage]
  constructor
  · rintro ⟨hz, hz'⟩
    refine ⟨hz, ?_⟩
    rcases hz' with h | ⟨u', hu', h⟩
    · exact absurd h Sum.inl_ne_inr
    · have h' : u' = (S.aU hp u).symm z := Sum.inl_injective h
      rw [← h']; exact hu'
  · rintro ⟨hz, hz'⟩
    exact ⟨hz, Or.inr ⟨_, hz', rfl⟩⟩

theorem transition_AP (u : U) (c : S.Punct hp) :
    IsOpen ((S.chart hp (Sum.inl u)).symm.trans (S.chart hp (Sum.inr c))).source ∧
      ContinuousOn ((S.chart hp (Sum.inl u)).symm.trans (S.chart hp (Sum.inr c)))
        ((S.chart hp (Sum.inl u)).symm.trans (S.chart hp (Sum.inr c))).source := by
  rw [source_AP]
  refine ⟨(S.aU hp u).continuousOn_symm.isOpen_inter_preimage (S.aU hp u).open_target
    (Datum.isOpen_image_M hp _), ?_⟩
  rintro z₀ ⟨hz₀, v₀, hv₀, hzv⟩
  have hsymm : ContinuousAt (S.aU hp u).symm z₀ :=
    (S.aU hp u).continuousOn_symm.continuousAt ((S.aU hp u).open_target.mem_nhds hz₀)
  have hF : ContinuousAt (fun z ↦ (S.D hp c.1).R v₀ ((S.D hp c.1).ψ
      (p ((S.aU hp u).symm z)))) z₀ := by
    have := Datum.continuousAt_R_ψ_p hp (D := S.D hp c.1) c.2.out hv₀
    rw [hzv] at this
    exact ContinuousAt.comp (f := (S.aU hp u).symm) this hsymm
  refine (hF.congr ?_).continuousWithinAt
  have hev := Datum.eventually_M_R hp (D := S.D hp c.1) c.2.out hv₀
  rw [hzv] at hev
  filter_upwards [hsymm.preimage_mem_nhds hev] with z hz
  obtain ⟨hzD, hzM⟩ := hz
  change _ = (S.pChart hp c) (Sum.inl ((S.aU hp u).symm z))
  conv_rhs => rw [← hzM]
  exact (S.pChart_inl_M hp c hzD).symm

theorem transition_PP (c c' : S.Punct hp) :
    IsOpen ((S.chart hp (Sum.inr c)).symm.trans (S.chart hp (Sum.inr c'))).source ∧
      ContinuousOn ((S.chart hp (Sum.inr c)).symm.trans (S.chart hp (Sum.inr c')))
        ((S.chart hp (Sum.inr c)).symm.trans (S.chart hp (Sum.inr c'))).source := by
  simp only [chart]
  by_cases hcc : c = c'
  · subst hcc
    have hsrc : ((S.pChart hp c).symm.trans (S.pChart hp c)).source =
        (S.pChart hp c).target := by
      ext v
      exact ⟨fun h ↦ h.1, fun hv ↦ ⟨hv, (S.pChart hp c).map_target hv⟩⟩
    rw [hsrc]
    have hopen : IsOpen (S.pChart hp c).target :=
      isOpen_lt (continuous_norm.pow _) continuous_const
    exact ⟨hopen, continuousOn_id.congr fun v hv ↦ (S.pChart hp c).right_inv hv⟩
  · have hsrc : ((S.pChart hp c).symm.trans (S.pChart hp c')).source = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro v ⟨hv, hv'⟩
      exact Set.disjoint_left.1 (S.pChart_source_disjoint hp hcc)
        ((S.pChart hp c).map_target hv) hv'
    rw [hsrc]
    exact ⟨isOpen_empty, continuousOn_empty _⟩

end Setup

end HurwitzPrymRexFill

end HodgeLean.Foundations.Program
