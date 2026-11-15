import HodgeLean.Foundations.Program.HurwitzPrymRexFillSmooth

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-rex`: topology of the filled surface

The filled surface `CC` (the filled set with the topology and charts of its chart core): the
inclusion of `U` is an open embedding, the map to `Y` is continuous, and `CC` is Hausdorff.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Topology Metric Set Complex Manifold HodgeLean.Foundations.Program.HurwitzPrymRexPunct
open scoped ContDiff

namespace HodgeLean.Foundations.Program

namespace HurwitzPrymRexFill

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y]
variable {B : Set Y} {G U : Type} [Group G] [TopologicalSpace U] [MulAction G U]
variable {p : U → {y : Y // y ∉ B}}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace Setup

variable (S : Setup E' p) (hp : IsQuotientCoveringMap p G) [Finite G] (κ : ℂ ≃L[ℂ] E)

/-- **The filled surface** with its topology and charts.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, Theorem 8.4 (filling the punctures). -/
def CC (_κ : ℂ ≃L[ℂ] E) : Type := S.C hp

instance : TopologicalSpace (S.CC hp κ) := (S.core hp κ).toTopologicalSpace

instance : ChartedSpace E (S.CC hp κ) := (S.core hp κ).toChartedSpace

/-- The inclusion of `U`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, Theorem 8.4 (filling the punctures). -/
def ι (u : U) : S.CC hp κ := Sum.inl u

/-- A new point.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, Theorem 8.4 (filling the punctures). -/
def ofP (c : S.Punct hp) : S.CC hp κ := Sum.inr c

/-- The map to `Y`: `p` on `U`, and `b` at the new points over `b`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, Theorem 8.4 (filling the punctures). -/
def f (x : S.CC hp κ) : Y := Sum.elim (fun u ↦ (p u).1) (fun c : S.Punct hp ↦ c.1.1) (x : S.C hp)

example (u : U) : S.f hp κ (S.ι hp κ u) = (p u).1 := rfl

example (c : S.Punct hp) : S.f hp κ (S.ofP hp κ c) = c.1.1 := rfl

theorem chartAt_apply (x y : S.CC hp κ) : chartAt E x y = κ (S.chart hp x y) := rfl

theorem chartAt_symm_apply (x : S.CC hp κ) (w : E) :
    (chartAt E x).symm w = (S.chart hp x).symm (κ.symm w) := rfl

theorem chartAt_source (x : S.CC hp κ) : (chartAt E x).source = (S.chart hp x).source := by
  change ((S.chart hp x).trans (κPE κ)).source = _
  simp [PartialEquiv.trans_source, κPE]

theorem chartAt_target (x : S.CC hp κ) :
    (chartAt E x).target = κ.symm ⁻¹' (S.chart hp x).target := by
  change ((S.chart hp x).trans (κPE κ)).target = _
  ext w
  simp [PartialEquiv.trans_target, κPE]

theorem ι_preimage_chart_source (u : U) :
    S.ι hp κ ⁻¹' (chartAt E (S.ι hp κ u)).source = (S.aU hp u).source := by
  rw [chartAt_source]
  ext w
  exact Sum.inl_injective.mem_set_image

theorem continuous_ι : Continuous (S.ι hp κ) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hsrc : S.ι hp κ ⁻¹' (chartAt E (S.ι hp κ u)).source ∈ 𝓝 u := by
    rw [ι_preimage_chart_source]
    exact (S.aU hp u).open_source.mem_nhds (S.mem_aU_source hp u)
  rw [(chartAt E (S.ι hp κ u)).continuousAt_iff_continuousAt_comp_left hsrc]
  have h : ContinuousAt (fun w ↦ κ (S.aU hp u w)) u :=
    κ.continuous.continuousAt.comp
      ((S.aU hp u).continuousOn.continuousAt
        ((S.aU hp u).open_source.mem_nhds (S.mem_aU_source hp u)))
  exact h

theorem isOpenMap_ι : IsOpenMap (S.ι hp κ) := by
  intro W hW
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨u, hu, rfl⟩
  set e := chartAt E (S.ι hp κ u)
  have hWs : IsOpen (W ∩ (S.aU hp u).source) := hW.inter (S.aU hp u).open_source
  set s : Set E := κ '' (S.aU hp u '' (W ∩ (S.aU hp u).source))
  have hs : IsOpen s := κ.toHomeomorph.isOpenMap _
    ((S.aU hp u).isOpen_image_of_subset_source hWs inter_subset_right)
  have hst : s ⊆ e.target := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    rw [chartAt_target]
    change κ.symm (κ (S.aU hp u w)) ∈ (S.aU hp u).target
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact (S.aU hp u).map_source hw.2
  have hopen : IsOpen (e.symm '' s) := e.isOpen_image_symm_of_subset_target hs hst
  have hsub : e.symm '' s ⊆ S.ι hp κ '' W := by
    rintro _ ⟨_, ⟨_, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
    refine ⟨w, hw.1, ?_⟩
    rw [chartAt_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
    change Sum.inl w = Sum.inl ((S.aU hp u).symm (S.aU hp u w))
    rw [(S.aU hp u).left_inv hw.2]
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨_, ⟨_, ⟨u, ⟨hu, S.mem_aU_source hp u⟩, rfl⟩, rfl⟩,
    ?_⟩) hsub
  rw [chartAt_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
  change Sum.inl ((S.aU hp u).symm (S.aU hp u u)) = Sum.inl u
  rw [(S.aU hp u).left_inv (S.mem_aU_source hp u)]

/-- **`U` is an open subset of the filled surface.** -/
theorem isOpenEmbedding_ι : IsOpenEmbedding (S.ι hp κ) :=
  .of_continuous_injective_isOpenMap (S.continuous_ι hp κ) Sum.inl_injective (S.isOpenMap_ι hp κ)

theorem f_eq_on_pChart (c : S.Punct hp) {x : S.C hp} (hx : x ∈ (S.pChart hp c).source) :
    S.f hp κ x = ξY S.κ' c.1.1 ((S.pChart hp c x) ^ (S.D hp c.1).e) := by
  rcases hx with hx | ⟨u, ⟨v, hv, rfl⟩, rfl⟩
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    change c.1.1 = ξY S.κ' c.1.1 ((S.pChart hp c (Sum.inr c)) ^ (S.D hp c.1).e)
    change c.1.1 = ξY S.κ' c.1.1 ((0 : ℂ) ^ (S.D hp c.1).e)
    rw [zero_pow (S.D hp c.1).e_pos.ne', ξY_zero]
  · change (p ((S.D hp c.1).M c.2.out v)).1 = _
    change _ = ξY S.κ' c.1.1 ((S.pChart hp c (Sum.inl ((S.D hp c.1).M c.2.out v))) ^ (S.D hp c.1).e)
    rw [S.pChart_inl_M hp c hv, S.val_p_M hp c.1 c.2.out hv]

theorem continuous_f : Continuous (S.f hp κ) := by
  rw [continuous_iff_continuousAt]
  rintro (u | c)
  · change ContinuousAt (S.f hp κ) (S.ι hp κ u)
    rw [← (S.isOpenEmbedding_ι hp κ).continuousAt_iff]
    exact (continuous_subtype_val.comp hp.continuous).continuousAt
  · set e := chartAt E (S.ofP hp κ c)
    have hsrc : e.source ∈ 𝓝 (S.ofP hp κ c) :=
      e.open_source.mem_nhds (_root_.mem_chart_source E _)
    have he0 : κ.symm (e (S.ofP hp κ c)) = 0 := by
      rw [chartAt_apply, ContinuousLinearEquiv.symm_apply_apply]; rfl
    have hF : ContinuousAt (fun w : E ↦ ξY S.κ' c.1.1 ((κ.symm w) ^ (S.D hp c.1).e))
        (e (S.ofP hp κ c)) := by
      have h1 : ContinuousAt (fun w : E ↦ (κ.symm w) ^ (S.D hp c.1).e) (e (S.ofP hp κ c)) :=
        (κ.symm.continuous.pow _).continuousAt
      have h2 : ContinuousAt (ξY S.κ' c.1.1) ((κ.symm (e (S.ofP hp κ c))) ^ (S.D hp c.1).e) := by
        rw [he0, zero_pow (S.D hp c.1).e_pos.ne']
        exact (continuousOn_ξY c.1.1).continuousAt ((isOpen_Tgt _).mem_nhds (zero_mem_Tgt _))
      exact ContinuousAt.comp (f := fun w : E ↦ (κ.symm w) ^ (S.D hp c.1).e) h2 h1
    have he : ContinuousAt e (S.ofP hp κ c) := e.continuousAt (_root_.mem_chart_source E _)
    refine (ContinuousAt.comp (f := e) hF he).congr ?_
    filter_upwards [hsrc] with x hx
    rw [chartAt_source] at hx
    have := S.f_eq_on_pChart hp κ c hx
    rw [this]
    change ξY S.κ' c.1.1 ((κ.symm (κ (S.pChart hp c x))) ^ (S.D hp c.1).e) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]

variable [T2Space Y]

instance : T2Space (S.CC hp κ) := by
  refine ⟨fun x y hxy ↦ ?_⟩
  by_cases hf : S.f hp κ x = S.f hp κ y
  · rcases x with u | c <;> rcases y with u' | c'
    · -- two points of `U` in one fibre
      have hpu : p u = p u' := Subtype.ext hf
      obtain ⟨g, hg⟩ := hp.apply_eq_iff_mem_orbit.1 hpu.symm
      replace hg : g • u = u' := hg
      have hg1 : g ≠ 1 := by
        rintro rfl
        apply hxy
        rw [one_smul] at hg
        change Sum.inl u = Sum.inl u'
        rw [hg]
      obtain ⟨W, hW, hWd⟩ := hp.disjoint u
      obtain ⟨W₀, hW₀W, hW₀o, huW₀⟩ := mem_nhds_iff.1 hW
      have := hp.toContinuousConstSMul
      refine ⟨S.ι hp κ '' W₀, S.ι hp κ '' ((g • ·) '' W₀), S.isOpenMap_ι hp κ _ hW₀o,
        S.isOpenMap_ι hp κ _ ((Homeomorph.smul g).isOpenMap _ hW₀o), ⟨u, huW₀, rfl⟩,
        ⟨_, ⟨u, huW₀, hg⟩, rfl⟩, ?_⟩
      rw [Set.disjoint_left]
      rintro _ ⟨a, ha, rfl⟩ ⟨_, ⟨a', ha', rfl⟩, hea⟩
      have hea' : g • a' = a := Sum.inl_injective hea
      exact hg1 (hWd g ⟨a, ⟨a', hW₀W ha', hea'⟩, hW₀W ha⟩)
    · have h : (p u).1 = c'.1.1 := hf
      exact absurd (h ▸ c'.1.2) (p u).2
    · have h : c.1.1 = (p u').1 := hf
      exact absurd (h ▸ c.1.2) (p u').2
    · -- two new points over one puncture
      have hcc : c ≠ c' := fun h ↦ hxy (congrArg Sum.inr h)
      refine ⟨(chartAt E (S.ofP hp κ c)).source,
        (chartAt E (S.ofP hp κ c')).source, (chartAt E _).open_source,
        (chartAt E _).open_source, _root_.mem_chart_source E _, _root_.mem_chart_source E _, ?_⟩
      rw [chartAt_source, chartAt_source]
      exact S.pChart_source_disjoint hp hcc
  · obtain ⟨O, O', hO, hO', hxO, hyO', hOO'⟩ := t2_separation hf
    exact ⟨S.f hp κ ⁻¹' O, S.f hp κ ⁻¹' O', hO.preimage (S.continuous_f hp κ),
      hO'.preimage (S.continuous_f hp κ), hxO, hyO', hOO'.preimage _⟩

/-! ## Connectedness -/

theorem chartAt_ofP_self (c : S.Punct hp) : chartAt E (S.ofP hp κ c) (S.ofP hp κ c) = 0 := by
  rw [chartAt_apply]
  change κ (S.pChart hp c (Sum.inr c)) = 0
  simp [pChart]

theorem ofP_mem_closure_range (c : S.Punct hp) : S.ofP hp κ c ∈ closure (range (S.ι hp κ)) := by
  set e := chartAt E (S.ofP hp κ c)
  have h0 : e (S.ofP hp κ c) = 0 := S.chartAt_ofP_self hp κ c
  have htgt : e.target ∈ 𝓝 (0 : E) := by
    rw [← h0]; exact e.open_target.mem_nhds (e.map_source (_root_.mem_chart_source E _))
  have hsymm : ContinuousAt e.symm 0 := by
    rw [← h0]
    exact e.continuousAt_symm (e.map_source (_root_.mem_chart_source E _))
  have hsymm0 : e.symm 0 = S.ofP hp κ c := by
    rw [← h0]; exact e.left_inv (_root_.mem_chart_source E _)
  have hg : ContinuousAt (fun z : ℂ ↦ e.symm (κ z)) 0 := by
    have : ContinuousAt e.symm (κ 0) := by rw [map_zero]; exact hsymm
    exact ContinuousAt.comp (f := fun z : ℂ ↦ κ z) this κ.continuous.continuousAt
  have hlim : Filter.Tendsto (fun z : ℂ ↦ e.symm (κ z)) (𝓝[≠] 0) (𝓝 (S.ofP hp κ c)) := by
    have := hg.tendsto
    rw [map_zero, hsymm0] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hlim ?_
  have hκt : ∀ᶠ z in 𝓝 (0 : ℂ), κ z ∈ e.target :=
    κ.continuous.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact htgt)
  filter_upwards [nhdsWithin_le_nhds hκt, self_mem_nhdsWithin] with z _ hz
  refine ⟨(S.D hp c.1).M c.2.out z, ?_⟩
  rw [chartAt_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
  exact (S.pChart_symm_of_ne hp hz).symm

theorem closure_range_ι : closure (range (S.ι hp κ)) = univ := by
  refine Set.eq_univ_of_forall fun x ↦ ?_
  rcases x with u | c
  · exact subset_closure ⟨u, rfl⟩
  · exact S.ofP_mem_closure_range hp κ c

instance [ConnectedSpace U] : ConnectedSpace (S.CC hp κ) := by
  rw [connectedSpace_iff_univ, ← S.closure_range_ι hp κ]
  exact (isConnected_range (S.continuous_ι hp κ)).closure

/-! ## Compactness -/

include hp in
theorem finite_fiber (y : {y : Y // y ∉ B}) : Finite (p ⁻¹' {y}) := by
  rcases (p ⁻¹' {y}).eq_empty_or_nonempty with h | ⟨u₀, hu₀⟩
  · rw [h]; exact Finite.of_subsingleton
  · refine Set.Finite.to_subtype ((Set.finite_range fun g : G ↦ g • u₀).subset ?_)
    intro u hu
    obtain ⟨g, hg⟩ := hp.apply_eq_iff_mem_orbit.1 (hu.trans hu₀.symm)
    exact ⟨g, hg⟩

omit [T2Space Y] in
theorem isCompact_K (b : B) :
    IsCompact {v : ℂ | ‖v‖ ^ (S.D hp b).e ≤ S.r b / 2} := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (continuous_norm.pow _) continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := max 1 (S.r b / 2))).subset ?_
  intro v hv
  rw [mem_closedBall_zero_iff]
  by_cases h1 : ‖v‖ ≤ 1
  · exact h1.trans (le_max_left _ _)
  · push_neg at h1
    exact (le_self_pow₀ h1.le (S.D hp b).e_pos.ne').trans (hv.trans (le_max_right _ _))

/-- **Near a puncture, the preimage lies in finitely many closed chart discs.** -/
theorem exists_compact_B (b : B) :
    ∃ N ∈ 𝓝 b.1, ∃ Q : Set (S.CC hp κ), IsCompact Q ∧ S.f hp κ ⁻¹' N ⊆ Q := by
  set K : Set ℂ := {v : ℂ | ‖v‖ ^ (S.D hp b).e ≤ S.r b / 2}
  have hr := S.hr b
  have hsub : ball (0 : ℂ) (S.r b / 2) ⊆ Tgt S.κ' b.1 :=
    (ball_subset_ball (by linarith)).trans (S.hTgt b)
  refine ⟨ξY S.κ' b.1 '' ball 0 (S.r b / 2), (isOpen_image_ξY hsub isOpen_ball).mem_nhds
    ⟨0, mem_ball_self (by linarith), ξY_zero _⟩,
    ⋃ q : G ⧸ Subgroup.zpowers (S.D hp b).h,
      (chartAt E (S.ofP hp κ ⟨b, q⟩)).symm '' (κ '' K), ?_, ?_⟩
  · refine isCompact_iUnion fun q ↦ ?_
    refine ((S.isCompact_K hp b).image κ.continuous).image_of_continuousOn
      ((chartAt E (S.ofP hp κ ⟨b, q⟩)).continuousOn_symm.mono ?_)
    rintro _ ⟨v, hv, rfl⟩
    rw [chartAt_target]
    change κ.symm (κ v) ∈ {v | ‖v‖ ^ (S.D hp b).e < S.r b}
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact lt_of_le_of_lt (show ‖v‖ ^ (S.D hp b).e ≤ S.r b / 2 from hv) (by linarith)
  · rintro (u | ⟨b', q⟩) ⟨z, hz, hfz⟩
    · -- a point of `U` over the punctured disc
      have hz0 : z ≠ 0 := by
        rintro rfl
        rw [ξY_zero] at hfz
        have h' : b.1 = (p u).1 := hfz
        exact (p u).2 (h' ▸ b.2)
      have hzr : z ∈ ball (0 : ℂ) (S.r b) \ {0} :=
        ⟨ball_subset_ball (by linarith) hz, hz0⟩
      have hpu : p u = (S.D hp b).ξ z := by
        apply Subtype.ext
        change (p u).1 = (ξB S.κ' B (p S.u₀) b.1 z : Y)
        rw [ξB_val (ξY_not_mem (S.havoid b) hzr)]
        exact hfz.symm
      obtain ⟨g, v, hv, hMv, hve⟩ := Datum.exists_M hp hzr hpu
      set q : G ⧸ Subgroup.zpowers (S.D hp b).h := QuotientGroup.mk g
      obtain ⟨j, hj⟩ : ∃ j : ℤ, q.out⁻¹ * g = (S.D hp b).h ^ j := by
        have : q.out⁻¹ * g ∈ Subgroup.zpowers (S.D hp b).h := by
          rw [← QuotientGroup.eq]
          exact QuotientGroup.out_eq' q
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 this
        exact ⟨j, hj.symm⟩
      have hg : g = q.out * (S.D hp b).h ^ j := by rw [← hj, mul_inv_cancel_left]
      rw [hg, Datum.M_mul_zpow hp _ hv] at hMv
      have hv' := Datum.mul_ζ_mem (D := S.D hp b) hv j
      refine mem_iUnion.2 ⟨q, κ (v * (S.D hp b).ζ ^ j), ⟨v * (S.D hp b).ζ ^ j, ?_, rfl⟩, ?_⟩
      · change ‖v * (S.D hp b).ζ ^ j‖ ^ (S.D hp b).e ≤ S.r b / 2
        rw [norm_mul, Datum.norm_ζ_pow, mul_one, ← norm_pow, hve]
        exact (mem_ball_zero_iff.1 hz).le
      · rw [chartAt_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
        change (S.pChart hp ⟨b, q⟩).symm _ = Sum.inl u
        rw [S.pChart_symm_of_ne hp hv'.1]
        exact congrArg Sum.inl hMv
    · -- a new point
      have hb' : b' = b := by
        have hz' : z ∈ ball (0 : ℂ) (S.r b) := ball_subset_ball (by linarith) hz
        have hz0 := S.havoid b z hz' (by rw [hfz]; exact b'.2)
        apply Subtype.ext
        have h' : b'.1 = ξY S.κ' b.1 z := hfz.symm
        rw [h', hz0, ξY_zero]
      subst hb'
      refine mem_iUnion.2 ⟨q, κ 0, ⟨0, ?_, rfl⟩, ?_⟩
      · change ‖(0 : ℂ)‖ ^ (S.D hp b').e ≤ S.r b' / 2
        rw [norm_zero, zero_pow (S.D hp b').e_pos.ne']
        linarith
      · rw [chartAt_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
        exact S.pChart_symm_zero hp ⟨b', q⟩

/-- **Over a point of `Y ∖ B`, the preimage of a compact evenly covered piece is compact.** -/
theorem exists_compact_reg [LocallyCompactSpace Y] (y : Y) (hy : y ∉ B) :
    ∃ N ∈ 𝓝 y, ∃ Q : Set (S.CC hp κ), IsCompact Q ∧ S.f hp κ ⁻¹' N ⊆ Q := by
  set y0 : {y : Y // y ∉ B} := ⟨y, hy⟩
  have hcov := hp.isCoveringMap
  obtain ⟨hdisc, V, hyV, hVo, hpVo, H, hH⟩ := hcov y0
  have := (isOpenEmbedding_val S.hBc).locallyCompactSpace
  obtain ⟨K, hKn, hKV, hKc⟩ := local_compact_nhds (hVo.mem_nhds hyV)
  have := finite_fiber hp y0
  -- the compact preimage of `K`
  set K' : Set V := {k | k.1 ∈ K}
  have hK' : IsCompact K' := by
    rw [Subtype.isCompact_iff]
    convert hKc
    ext k
    exact ⟨fun ⟨k', hk', hkk⟩ ↦ hkk ▸ hk', fun hk ↦ ⟨⟨k, hKV hk⟩, hk, rfl⟩⟩
  have hpre : p ⁻¹' K = Subtype.val '' (H.symm '' (K' ×ˢ univ)) := by
    ext u
    constructor
    · intro hu
      refine ⟨H.symm (H ⟨u, hKV hu⟩), ⟨H ⟨u, hKV hu⟩, ⟨?_, trivial⟩, rfl⟩, ?_⟩
      · change (H ⟨u, hKV hu⟩).1.1 ∈ K
        rw [hH]; exact hu
      · rw [H.symm_apply_apply]
    · rintro ⟨w, ⟨z, ⟨hz1, -⟩, rfl⟩, rfl⟩
      change p (H.symm z).1 ∈ K
      have := hH (H.symm z)
      rw [H.apply_symm_apply] at this
      rw [← this]
      exact hz1
  have hpc : IsCompact (p ⁻¹' K) := by
    rw [hpre]
    exact ((hK'.prod isCompact_univ).image H.symm.continuous).image continuous_subtype_val
  refine ⟨Subtype.val '' interior K, ?_, S.ι hp κ '' (p ⁻¹' K),
    hpc.image (S.continuous_ι hp κ), ?_⟩
  · exact ((isOpenEmbedding_val S.hBc).isOpenMap _ isOpen_interior).mem_nhds
      ⟨y0, mem_interior_iff_mem_nhds.2 hKn, rfl⟩
  · rintro (u | c) ⟨k, hk, hfk⟩
    · refine ⟨u, ?_, rfl⟩
      have : p u = k := Subtype.ext hfk.symm
      change p u ∈ K
      rw [this]; exact interior_subset hk
    · have h' : c.1.1 = k.1 := hfk.symm
      exact absurd (h' ▸ c.1.2) k.2

instance [CompactSpace Y] [LocallyCompactSpace Y] : CompactSpace (S.CC hp κ) := by
  have hex : ∀ y : Y, ∃ N ∈ 𝓝 y, ∃ Q : Set (S.CC hp κ), IsCompact Q ∧ S.f hp κ ⁻¹' N ⊆ Q :=
    fun y ↦ by
      by_cases hy : y ∈ B
      · exact S.exists_compact_B hp κ ⟨y, hy⟩
      · exact S.exists_compact_reg hp κ y hy
  choose N hN Q hQ hNQ using hex
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover N fun y _ ↦ hN y
  refine ⟨(t.isCompact_biUnion fun y _ ↦ hQ y).of_isClosed_subset isClosed_univ fun x _ ↦ ?_⟩
  obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.1 (ht.2 (mem_univ (S.f hp κ x)))
  exact mem_iUnion₂.2 ⟨y, hyt, hNQ y hy⟩

end Setup

end HurwitzPrymRexFill

end HodgeLean.Foundations.Program
