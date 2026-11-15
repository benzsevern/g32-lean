import HodgeLean.Foundations.Program.HurwitzPrymDefs

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-cov`: local theory of holomorphic maps of Riemann surfaces

For a holomorphic `f : C → Y` and `x : C`, the map written in the extended charts at `x` and
`f x` is analytic on the open set `b4cov_good E E' f x` of chart points whose image stays in the chart
at `f x`. From this: a map that is locally constant somewhere on a connected surface is constant
(identity theorem in charts), so a non-constant map has positive ramification index everywhere.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Manifold Set Filter Topology
open scoped ContDiff

namespace HodgeLean.Foundations.Program

section Local

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y]

/-- The chart points at `x` whose image under `f` lies in the chart at `f x`. -/
def b4cov_good (E E' : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E C]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [ChartedSpace E' Y] (f : C → Y) (x : C) : Set E :=
  (extChartAt 𝓘(ℂ, E) x).target ∩
    (extChartAt 𝓘(ℂ, E) x).symm ⁻¹' (f ⁻¹' (extChartAt 𝓘(ℂ, E') (f x)).source)

omit [IsManifold 𝓘(ℂ, E) ω C] [IsManifold 𝓘(ℂ, E') ω Y] in
theorem b4cov_good_isOpen (f : C → Y) (hf : Continuous f) (x : C) :
    IsOpen (b4cov_good E E' f x) :=
  (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x)
    (hf.isOpen_preimage _ (isOpen_extChartAt_source _))

omit [IsManifold 𝓘(ℂ, E) ω C] [IsManifold 𝓘(ℂ, E') ω Y] in
theorem b4cov_mem_good (f : C → Y) (x : C) : extChartAt 𝓘(ℂ, E) x x ∈ b4cov_good E E' f x := by
  refine ⟨mem_extChartAt_target x, ?_⟩
  simp only [mem_preimage, extChartAt_to_inv x]
  exact mem_extChartAt_source (f x)

omit [IsManifold 𝓘(ℂ, E) ω C] [IsManifold 𝓘(ℂ, E') ω Y] in
theorem b4cov_good_nhds (f : C → Y) (hf : Continuous f) (x : C) :
    b4cov_good E E' f x ∈ 𝓝 (extChartAt 𝓘(ℂ, E) x x) :=
  (b4cov_good_isOpen f hf x).mem_nhds (b4cov_mem_good (E' := E') f x)

omit [IsManifold 𝓘(ℂ, E) ω C] [IsManifold 𝓘(ℂ, E') ω Y] in
/-- The source points at `x` whose image lies in the chart at `f x`, a neighborhood of `x`. -/
theorem b4cov_source_nhds (f : C → Y) (hf : Continuous f) (x : C) :
    (extChartAt 𝓘(ℂ, E) x).source ∩ f ⁻¹' (extChartAt 𝓘(ℂ, E') (f x)).source ∈ 𝓝 x :=
  inter_mem (extChartAt_source_mem_nhds x)
    (hf.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (f x)))

omit [IsManifold 𝓘(ℂ, E) ω C] [IsManifold 𝓘(ℂ, E') ω Y] in
/-- `f` is recovered from its expression in charts on the chart domain. -/
theorem b4cov_eq_symm_written (f : C → Y) (x x' : C)
    (hx' : x' ∈ (extChartAt 𝓘(ℂ, E) x).source)
    (hfx' : f x' ∈ (extChartAt 𝓘(ℂ, E') (f x)).source) :
    f x' = (extChartAt 𝓘(ℂ, E') (f x)).symm
      (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f (extChartAt 𝓘(ℂ, E) x x')) := by
  simp only [writtenInExtChartAt, Function.comp_apply, (extChartAt 𝓘(ℂ, E) x).left_inv hx',
    (extChartAt 𝓘(ℂ, E') (f x)).left_inv hfx']

/-- **The chart expression of a holomorphic map is analytic** on `b4cov_good E E' f x`. -/
theorem b4cov_analyticOnNhd (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (x : C) :
    AnalyticOnNhd ℂ (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f) (b4cov_good E E' f x) := by
  intro z hz
  have h1 : (extChartAt 𝓘(ℂ, E) x).symm z ∈ (chartAt E x).source := by
    rw [← extChartAt_source 𝓘(ℂ, E)]
    exact (extChartAt 𝓘(ℂ, E) x).map_target hz.1
  have h2 : f ((extChartAt 𝓘(ℂ, E) x).symm z) ∈ (chartAt E' (f x)).source := by
    rw [← extChartAt_source 𝓘(ℂ, E')]
    exact hz.2
  have := ((contMDiffAt_iff_of_mem_source h1 h2).1 (hf _)).2
  rw [(extChartAt 𝓘(ℂ, E) x).right_inv hz.1, modelWithCornersSelf_coe, range_id,
    contDiffWithinAt_univ] at this
  exact this.analyticAt

/-- **A map locally constant at one point of a connected surface is constant** (identity theorem
in the charts). -/
theorem b4cov_const_of_eventuallyConst [ConnectedSpace C] [CompleteSpace E']
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (x₀ : C)
    (h₀ : ∀ᶠ y in 𝓝 x₀, f y = f x₀) (x x' : C) : f x = f x' := by
  let S : Set C := {x | ∀ᶠ y in 𝓝 x, f y = f x}
  have hSo : IsOpen S := by
    refine isOpen_iff_mem_nhds.2 fun x hx ↦ ?_
    filter_upwards [hx.eventually_nhds] with y hy
    filter_upwards [hy] with z hz
    rw [hz]
    exact hy.self_of_nhds.symm ▸ rfl
  have hSc : IsClosed S := by
    refine isClosed_of_closure_subset fun x hx ↦ ?_
    set φ := extChartAt 𝓘(ℂ, E) x
    set ψ := extChartAt 𝓘(ℂ, E') (f x)
    set g := writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f
    obtain ⟨r, hr, hrg⟩ := Metric.isOpen_iff.1 (b4cov_good_isOpen f hf.continuous x) (φ x)
      (b4cov_mem_good (E' := E') f x)
    have hball : AnalyticOnNhd ℂ g (Metric.ball (φ x) r) :=
      (b4cov_analyticOnNhd f hf x).mono hrg
    have hN : (extChartAt 𝓘(ℂ, E) x).source ∩ f ⁻¹' (extChartAt 𝓘(ℂ, E') (f x)).source ∩
        φ ⁻¹' Metric.ball (φ x) r ∈ 𝓝 x :=
      inter_mem (b4cov_source_nhds f hf.continuous x)
        ((continuousAt_extChartAt x).preimage_mem_nhds (Metric.ball_mem_nhds _ hr))
    obtain ⟨x', ⟨⟨hx's, hx'f⟩, hx'b⟩, hx'S⟩ := mem_closure_iff_nhds.1 hx _ hN
    have hgc : g =ᶠ[𝓝 (φ x')] fun _ ↦ ψ (f x') := by
      have hc : ContinuousAt φ.symm (φ x') :=
        continuousAt_extChartAt_symm'' (φ.map_source hx's)
      have := hc.preimage_mem_nhds (by rw [φ.left_inv hx's]; exact hx'S)
      filter_upwards [this] with z hz
      exact congrArg ψ hz
    have hEq := hball.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      (convex_ball _ _).isPreconnected hx'b hgc
    have hNx : (extChartAt 𝓘(ℂ, E) x).source ∩ f ⁻¹' (extChartAt 𝓘(ℂ, E') (f x)).source ∩
        φ ⁻¹' Metric.ball (φ x) r ∈ 𝓝 x := hN
    have key : ∀ y ∈ (extChartAt 𝓘(ℂ, E) x).source ∩ f ⁻¹' (extChartAt 𝓘(ℂ, E') (f x)).source ∩
        φ ⁻¹' Metric.ball (φ x) r, f y = f x' := by
      rintro y ⟨⟨hys, hyf⟩, hyb⟩
      rw [b4cov_eq_symm_written f x y hys hyf, b4cov_eq_symm_written f x x' hx's hx'f]
      exact congrArg ψ.symm ((hEq hyb).trans (hEq hx'b).symm)
    have hxx' : f x = f x' := key x (mem_of_mem_nhds hNx)
    show ∀ᶠ y in 𝓝 x, f y = f x
    filter_upwards [hNx] with y hy
    rw [key y hy, hxx']
  have hS : S = univ := (IsClopen.eq_univ ⟨hSc, hSo⟩ ⟨x₀, h₀⟩)
  have hlc : IsLocallyConstant f := (IsLocallyConstant.iff_eventually_eq f).2 fun x ↦ by
    have : x ∈ S := hS ▸ trivial
    exact this
  exact hlc.apply_eq_of_preconnectedSpace x x'

/-- An analytic map whose derivatives of order `≥ 1` all vanish at `z₀` is constant near `z₀`. -/
theorem b4cov_eventually_const_of_iteratedFDeriv {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {g : E → F} {z₀ : E} (hg : AnalyticAt ℂ g z₀)
    (h : ∀ n, 1 ≤ n → iteratedFDeriv ℂ n g z₀ = 0) : ∀ᶠ z in 𝓝 z₀, g z = g z₀ := by
  obtain ⟨p, r, hp⟩ := hg
  have hmem : ∀ᶠ z in 𝓝 z₀, z - z₀ ∈ Metric.eball (0 : E) r :=
    (continuous_sub_right z₀).continuousAt.preimage_mem_nhds
      (by simpa using Metric.eball_mem_nhds (0 : E) hp.r_pos)
  filter_upwards [hmem] with z hz
  have hs := hp.hasSum_iteratedFDeriv hz
  rw [add_sub_cancel] at hs
  refine hs.unique ?_
  convert hasSum_single (f := fun n ↦ ((n.factorial : ℂ))⁻¹ •
    iteratedFDeriv ℂ n g z₀ fun _ ↦ z - z₀) 0 fun n hn ↦ by
      simp [h n (Nat.one_le_iff_ne_zero.2 hn)]
  simp [iteratedFDeriv_zero_apply]

/-- **The ramification index of a non-constant holomorphic map is positive.** -/
theorem b4cov_ramIndex_pos [ConnectedSpace C] [CompleteSpace E']
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hnc : ∃ x x', f x ≠ f x') (x : C) :
    1 ≤ b4_ramIndex E E' f x := by
  by_contra hlt
  have h0 : ∀ n, 1 ≤ n → iteratedFDeriv ℂ n (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f)
      (extChartAt 𝓘(ℂ, E) x x) = 0 := by
    intro n hn
    by_contra hne
    exact hlt ((le_csInf ⟨n, hn, hne⟩ fun _ hm ↦ hm.1))
  have hev := b4cov_eventually_const_of_iteratedFDeriv
    (b4cov_analyticOnNhd f hf x _ (b4cov_mem_good (E' := E') f x)) h0
  have hfx : ∀ᶠ y in 𝓝 x, f y = f x := by
    have hc := (continuousAt_extChartAt (I := 𝓘(ℂ, E)) x).preimage_mem_nhds hev
    filter_upwards [hc, b4cov_source_nhds (E := E) (E' := E') f hf.continuous x] with y hy hys
    rw [b4cov_eq_symm_written f x y hys.1 hys.2, mem_preimage.1 hy,
      ← b4cov_eq_symm_written f x x (mem_extChartAt_source x) (mem_extChartAt_source (f x))]
  obtain ⟨a, b, hab⟩ := hnc
  exact hab (b4cov_const_of_eventuallyConst f hf x hfx a b)

omit [IsManifold 𝓘(ℂ, E) ω C] [IsManifold 𝓘(ℂ, E') ω Y] in
/-- If the chart expression at `x` is constant near the chart point, `f` is constant near `x`. -/
theorem b4cov_eventually_of_written (f : C → Y) (hf : Continuous f) (x : C)
    (h : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, E) x x), writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f z =
      writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f (extChartAt 𝓘(ℂ, E) x x)) :
    ∀ᶠ y in 𝓝 x, f y = f x := by
  have hc := (continuousAt_extChartAt (I := 𝓘(ℂ, E)) x).preimage_mem_nhds h
  filter_upwards [hc, b4cov_source_nhds (E := E) (E' := E') f hf x] with y hy hys
  rw [b4cov_eq_symm_written f x y hys.1 hys.2, mem_preimage.1 hy,
    ← b4cov_eq_symm_written f x x (mem_extChartAt_source x) (mem_extChartAt_source (f x))]

/-- **Isolated zeros in dimension one**: an analytic map on a complex line whose zeros accumulate
at `z₀` vanishes near `z₀`. -/
theorem b4cov_eventually_zero_of_frequently (hE : Module.finrank ℂ E = 1) {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {k : E → F} {z₀ : E}
    (hk : AnalyticAt ℂ k z₀) (hfr : ∃ᶠ z in 𝓝[≠] z₀, k z = 0) : ∀ᶠ z in 𝓝 z₀, k z = 0 := by
  have : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  let e : ℂ ≃L[ℂ] E := ContinuousLinearEquiv.ofFinrankEq (by rw [hE, Module.finrank_self])
  let Φ : ℂ ≃ₜ E := e.toHomeomorph.trans (Homeomorph.addLeft z₀)
  have hΦ : ∀ t, Φ t = z₀ + e t := fun t ↦ rfl
  have hΦ0 : Φ 0 = z₀ := by simp [hΦ]
  have hh : AnalyticAt ℂ (k ∘ Φ) 0 := by
    have ha : AnalyticAt ℂ (⇑Φ) 0 := by
      have : (⇑Φ) = fun t ↦ z₀ + e t := rfl
      rw [this]
      exact analyticAt_const.add (e.toContinuousLinearMap.analyticAt 0)
    exact (show AnalyticAt ℂ k (Φ 0) by rw [hΦ0]; exact hk).comp ha
  rcases hh.eventually_eq_zero_or_eventually_ne_zero with h | h
  · rw [← hΦ0, ← Φ.map_nhds_eq]
    exact h
  · rw [← hΦ0, ← Φ.map_punctured_nhds_eq] at hfr
    obtain ⟨t, ht, ht'⟩ := ((Filter.frequently_map.1 hfr).and_eventually h).exists
    exact absurd ht ht'

omit [IsManifold 𝓘(ℂ, E) ω C] [IsManifold 𝓘(ℂ, E') ω Y] in
/-- Points accumulating at `x` give chart points accumulating at the chart point. -/
theorem b4cov_frequently_chart (f : C → Y) (hf : Continuous f) (x : C) {P : C → Prop}
    (h : ∃ᶠ y in 𝓝[≠] x, P y) :
    ∃ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, E) x x),
      z ∈ b4cov_good E E' f x ∧ P ((extChartAt 𝓘(ℂ, E) x).symm z) := by
  rw [Filter.frequently_iff] at h ⊢
  intro U hU
  obtain ⟨V, hV, hVU⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hU
  have hW : (extChartAt 𝓘(ℂ, E) x) ⁻¹' (V ∩ b4cov_good E E' f x) ∩
      (extChartAt 𝓘(ℂ, E) x).source ∩ {x}ᶜ ∈ 𝓝[≠] x :=
    inter_mem (mem_nhdsWithin_of_mem_nhds (inter_mem ((continuousAt_extChartAt x).preimage_mem_nhds
      (inter_mem hV (b4cov_good_nhds f hf x))) (extChartAt_source_mem_nhds x)))
      self_mem_nhdsWithin
  obtain ⟨y, ⟨⟨⟨hyV, hyg⟩, hys⟩, hyx⟩, hP⟩ := h hW
  refine ⟨extChartAt 𝓘(ℂ, E) x y, hVU ⟨hyV, fun hxy ↦ hyx ?_⟩, hyg, ?_⟩
  · exact (extChartAt 𝓘(ℂ, E) x).injOn hys (mem_extChartAt_source x) hxy
  · rwa [(extChartAt 𝓘(ℂ, E) x).left_inv hys]

omit [IsManifold 𝓘(ℂ, E) ω C] [IsManifold 𝓘(ℂ, E') ω Y] in
theorem b4cov_written_apply (f : C → Y) (x : C) (z : E) :
    writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f z =
      extChartAt 𝓘(ℂ, E') (f x) (f ((extChartAt 𝓘(ℂ, E) x).symm z)) := rfl

/-- **Fibres of a non-constant holomorphic map of compact surfaces are finite.** -/
theorem b4cov_fiber_finite [CompactSpace C] [ConnectedSpace C] [T2Space Y] [CompleteSpace E']
    (hE : Module.finrank ℂ E = 1) (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (hnc : ∃ x x', f x ≠ f x') (y : Y) : (f ⁻¹' {y}).Finite := by
  by_contra hinf
  obtain ⟨x, -, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf isCompact_univ
    (subset_univ _)
  have hxy : f x = y :=
    (isClosed_singleton.preimage hf.continuous).closure_subset
      (mem_closure_iff_clusterPt.2 hx.clusterPt)
  have hfr := b4cov_frequently_chart (E := E) (E' := E') f hf.continuous x
    (accPt_iff_frequently_nhdsNE.1 hx)
  set g := writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f
  have hk : AnalyticAt ℂ (fun z ↦ g z - g (extChartAt 𝓘(ℂ, E) x x)) (extChartAt 𝓘(ℂ, E) x x) :=
    (b4cov_analyticOnNhd f hf x _ (b4cov_mem_good (E' := E') f x)).sub analyticAt_const
  have hfr' : ∃ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, E) x x),
      g z - g (extChartAt 𝓘(ℂ, E) x x) = 0 := by
    refine hfr.mono fun z hz ↦ ?_
    rw [sub_eq_zero]
    change extChartAt 𝓘(ℂ, E') (f x) (f ((extChartAt 𝓘(ℂ, E) x).symm z)) =
      extChartAt 𝓘(ℂ, E') (f x) (f ((extChartAt 𝓘(ℂ, E) x).symm (extChartAt 𝓘(ℂ, E) x x)))
    rw [Set.mem_singleton_iff.1 hz.2, extChartAt_to_inv, hxy]
  have hev := b4cov_eventually_zero_of_frequently hE hk hfr'
  have hfx := b4cov_eventually_of_written f hf.continuous x (hev.mono fun z hz ↦ sub_eq_zero.1 hz)
  obtain ⟨a, b, hab⟩ := hnc
  exact hab (b4cov_const_of_eventuallyConst f hf x hfx a b)

section CompZero

variable {V₁ V₂ W₁ W₂ W₃ : Type*} [TopologicalSpace V₁] [AddCommGroup V₁] [Module ℂ V₁]
  [TopologicalSpace V₂] [AddCommGroup V₂] [Module ℂ V₂] [TopologicalSpace W₁] [AddCommGroup W₁]
  [Module ℂ W₁] [TopologicalSpace W₂] [AddCommGroup W₂] [Module ℂ W₂] [TopologicalSpace W₃]
  [AddCommGroup W₃] [Module ℂ W₃]

theorem b4cov_equiv_comp_eq_zero_iff (e₁ : W₁ ≃L[ℂ] W₂) (D : V₂ →L[ℂ] W₁) (e₂ : V₁ ≃L[ℂ] V₂) :
    (e₁ : W₁ →L[ℂ] W₂) ∘L (D ∘L (e₂ : V₁ →L[ℂ] V₂)) = 0 ↔ D = 0 := by
  constructor
  · intro h
    ext v
    have := congrArg (fun L ↦ L (e₂.symm v)) h
    simpa using this
  · intro h
    rw [h]
    simp

theorem b4cov_equiv_comp_eq_zero_iff₃ (e₀ : W₂ ≃L[ℂ] W₃) (e₁ : W₁ ≃L[ℂ] W₂) (D : V₂ →L[ℂ] W₁)
    (e₂ : V₁ ≃L[ℂ] V₂) :
    (e₀ : W₂ →L[ℂ] W₃) ∘L ((e₁ : W₁ →L[ℂ] W₂) ∘L (D ∘L (e₂ : V₁ →L[ℂ] V₂))) = 0 ↔ D = 0 := by
  rw [← b4cov_equiv_comp_eq_zero_iff e₁ D e₂]
  constructor
  · intro h
    ext v
    have := congrArg (fun L ↦ L v) h
    simpa using this
  · intro h
    rw [h]
    simp

end CompZero

/-- **The derivative in the charts at `x`**: at a point `x'` of the chart domain, `df_{x'} = 0`
iff the derivative of the chart expression at `x` vanishes at the chart point of `x'`. -/
theorem b4cov_mfderiv_eq_zero_iff (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (x x' : C)
    (hx' : x' ∈ (extChartAt 𝓘(ℂ, E) x).source)
    (hfx' : f x' ∈ (extChartAt 𝓘(ℂ, E') (f x)).source) :
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x' = 0 ↔
      fderiv ℂ (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f) (extChartAt 𝓘(ℂ, E) x x') = 0 := by
  have hinv : (extChartAt 𝓘(ℂ, E) x).symm (extChartAt 𝓘(ℂ, E) x x') = x' :=
    (extChartAt 𝓘(ℂ, E) x).left_inv hx'
  have hgood : extChartAt 𝓘(ℂ, E) x x' ∈ b4cov_good E E' f x := by
    refine ⟨(extChartAt 𝓘(ℂ, E) x).map_source hx', ?_⟩
    rw [mem_preimage, mem_preimage, hinv]
    exact hfx'
  have hg : DifferentiableAt ℂ (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f)
      (extChartAt 𝓘(ℂ, E) x x') :=
    (b4cov_analyticOnNhd f hf x _ hgood).differentiableAt
  have hopen : IsOpen ((extChartAt 𝓘(ℂ, E) x).source ∩
      f ⁻¹' (extChartAt 𝓘(ℂ, E') (f x)).source) :=
    (isOpen_extChartAt_source x).inter (hf.continuous.isOpen_preimage _
      (isOpen_extChartAt_source _))
  have heq : f =ᶠ[𝓝 x'] (extChartAt 𝓘(ℂ, E') (f x)).symm ∘
      writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f ∘ extChartAt 𝓘(ℂ, E) x := by
    filter_upwards [hopen.mem_nhds ⟨hx', hfx'⟩] with y hy
    exact b4cov_eq_symm_written f x y hy.1 hy.2
  have hmem : writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f (extChartAt 𝓘(ℂ, E) x x') ∈
      (extChartAt 𝓘(ℂ, E') (f x)).target := by
    rw [b4cov_written_apply, hinv]
    exact (extChartAt 𝓘(ℂ, E') (f x)).map_source hfx'
  have hψ : MDifferentiableAt 𝓘(ℂ, E') 𝓘(ℂ, E') (extChartAt 𝓘(ℂ, E') (f x)).symm
      (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f (extChartAt 𝓘(ℂ, E) x x')) := by
    have := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℂ, E')) hmem
    rwa [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] at this
  have hφ : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E) (extChartAt 𝓘(ℂ, E) x) x' :=
    mdifferentiableAt_extChartAt (by rwa [← extChartAt_source 𝓘(ℂ, E)])
  have hgm := hg.mdifferentiableAt
  have hA : (mfderiv 𝓘(ℂ, E') 𝓘(ℂ, E') (extChartAt 𝓘(ℂ, E') (f x)).symm
      (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f (extChartAt 𝓘(ℂ, E) x x'))).IsInvertible := by
    have := isInvertible_mfderivWithin_extChartAt_symm (I := 𝓘(ℂ, E')) hmem
    rwa [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at this
  have hB : (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (extChartAt 𝓘(ℂ, E) x) x').IsInvertible :=
    isInvertible_mfderiv_extChartAt hx'
  rw [heq.mfderiv_eq, mfderiv_comp x' hψ (hgm.comp x' hφ), mfderiv_comp x' hgm hφ,
    mfderiv_eq_fderiv]
  obtain ⟨Ae, hAe⟩ := hA
  obtain ⟨Be, hBe⟩ := hB
  simp only [Function.comp_apply] at hAe ⊢
  rw [← hAe, ← hBe, b4cov_equiv_comp_eq_zero_iff₃, b4cov_equiv_comp_eq_zero_iff]

/-- **The critical points of a non-constant holomorphic map of compact surfaces are finite.** -/
theorem b4cov_critical_finite [CompactSpace C] [ConnectedSpace C] [CompleteSpace E']
    (hE : Module.finrank ℂ E = 1) (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (hnc : ∃ x x', f x ≠ f x') : {x | mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x = 0}.Finite := by
  by_contra hinf
  obtain ⟨x, -, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf isCompact_univ
    (subset_univ _)
  have hfr := b4cov_frequently_chart (E := E) (E' := E') f hf.continuous x
    (accPt_iff_frequently_nhdsNE.1 hx)
  have han := b4cov_analyticOnNhd f hf x
  have hD : AnalyticAt ℂ (fderiv ℂ (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f))
      (extChartAt 𝓘(ℂ, E) x x) := han.fderiv _ (b4cov_mem_good (E' := E') f x)
  have hfr' : ∃ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, E) x x),
      fderiv ℂ (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f) z = 0 := by
    refine hfr.mono fun z hz ↦ ?_
    have h1 : (extChartAt 𝓘(ℂ, E) x).symm z ∈ (extChartAt 𝓘(ℂ, E) x).source :=
      (extChartAt 𝓘(ℂ, E) x).map_target hz.1.1
    have := (b4cov_mfderiv_eq_zero_iff f hf x _ h1 hz.1.2).1 hz.2
    rwa [(extChartAt 𝓘(ℂ, E) x).right_inv hz.1.1] at this
  have hev := b4cov_eventually_zero_of_frequently hE hD hfr'
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1
    (hev.and (b4cov_good_nhds (E' := E') f hf.continuous x))
  have hconst : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, E) x x),
      writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f z =
        writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f (extChartAt 𝓘(ℂ, E) x x) := by
    filter_upwards [Metric.ball_mem_nhds _ hr] with z hz
    refine (convex_ball _ r).is_const_of_fderivWithin_eq_zero (𝕜 := ℂ) (fun w hw ↦ ?_) (fun w hw ↦ ?_) hz
      (Metric.mem_ball_self hr)
    · exact (han w (hball w hw).2).differentiableAt.differentiableWithinAt
    · rw [fderivWithin_of_isOpen Metric.isOpen_ball hw]
      exact (hball w hw).1
  have hfx := b4cov_eventually_of_written f hf.continuous x hconst
  obtain ⟨a, b, hab⟩ := hnc
  exact hab (b4cov_const_of_eventuallyConst f hf x hfx a b)

omit [IsManifold 𝓘(ℂ, E) ω C] [IsManifold 𝓘(ℂ, E') ω Y] in
/-- `f` near `x` is the chart expression read through the charts. -/
theorem b4cov_map_nhds_eq (f : C → Y) (hf : Continuous f) (x : C) :
    map f (𝓝 x) = map ((extChartAt 𝓘(ℂ, E') (f x)).symm ∘
      writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f) (𝓝 (extChartAt 𝓘(ℂ, E) x x)) := by
  rw [← map_extChartAt_nhds_of_boundaryless (I := 𝓘(ℂ, E)) x, map_map]
  refine Filter.map_congr ?_
  filter_upwards [b4cov_source_nhds (E := E) (E' := E') f hf x] with y hy
  exact b4cov_eq_symm_written f x y hy.1 hy.2

/-- **Open mapping**: a non-constant holomorphic map of a connected surface sends every
neighborhood of `x` onto a neighborhood of `f x`. -/
theorem b4cov_nhds_le_map [ConnectedSpace C] (hE' : Module.finrank ℂ E' = 1)
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hnc : ∃ x x', f x ≠ f x') (x : C) :
    𝓝 (f x) ≤ map f (𝓝 x) := by
  have : FiniteDimensional ℂ E' := Module.finite_of_finrank_eq_succ hE'
  have := FiniteDimensional.complete ℂ E'
  let L : E' ≃L[ℂ] ℂ := ContinuousLinearEquiv.ofFinrankEq (by rw [hE', Module.finrank_self])
  have han := b4cov_analyticOnNhd f hf x _ (b4cov_mem_good (E' := E') f x)
  have hk : AnalyticAt ℂ (L ∘ writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f)
      (extChartAt 𝓘(ℂ, E) x x) :=
    (L.toContinuousLinearMap.analyticAt _).comp han
  rcases hk.eventually_constant_or_nhds_le_map_nhds with h | h
  · exfalso
    have hg := h.mono fun z hz ↦ L.injective hz
    have hfx := b4cov_eventually_of_written f hf.continuous x hg
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (b4cov_const_of_eventuallyConst f hf x hfx a b)
  · have h1 : 𝓝 (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f (extChartAt 𝓘(ℂ, E) x x)) ≤
        map (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f) (𝓝 (extChartAt 𝓘(ℂ, E) x x)) := by
      have h2 := map_mono (m := L.symm) h
      rw [L.symm.map_nhds_eq, map_map] at h2
      simpa [Function.comp_def] using h2
    have hfx : (extChartAt 𝓘(ℂ, E') (f x)).symm
        (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f (extChartAt 𝓘(ℂ, E) x x)) = f x := by
      rw [b4cov_written_apply, extChartAt_to_inv, extChartAt_to_inv]
    have h3 := map_mono (m := (extChartAt 𝓘(ℂ, E') (f x)).symm) h1
    rw [map_map, ← b4cov_map_nhds_eq f hf.continuous x, b4cov_written_apply,
      extChartAt_to_inv] at h3
    have h4 := map_extChartAt_symm_nhdsWithin_range (I := 𝓘(ℂ, E')) (f x)
    rw [modelWithCornersSelf_coe, range_id, nhdsWithin_univ] at h4
    rwa [h4] at h3

/-- **A non-constant holomorphic map of compact connected surfaces is surjective.** -/
theorem b4cov_surjective [CompactSpace C] [ConnectedSpace C] [T2Space Y] [ConnectedSpace Y]
    (hE' : Module.finrank ℂ E' = 1) (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (hnc : ∃ x x', f x ≠ f x') : Function.Surjective f := by
  obtain ⟨x₀, -⟩ := id hnc
  have hopen : IsOpen (range f) := isOpen_iff_mem_nhds.2 fun y ⟨x, hx⟩ ↦
    hx ▸ b4cov_nhds_le_map hE' f hf hnc x range_mem_map
  have hclosed : IsClosed (range f) := (isCompact_range hf.continuous).isClosed
  exact range_eq_univ.1 (IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨f x₀, x₀, rfl⟩)

/-- A nonzero linear map between complex lines is an isomorphism. -/
theorem b4cov_bijective_of_ne_zero (hE : Module.finrank ℂ E = 1) (hE' : Module.finrank ℂ E' = 1)
    (D : E →L[ℂ] E') (hD : D ≠ 0) : Function.Bijective D := by
  have : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  have : FiniteDimensional ℂ E' := Module.finite_of_finrank_eq_succ hE'
  have hsurj : Function.Surjective (D : E →ₗ[ℂ] E') := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Submodule.finrank_le (LinearMap.range (D : E →ₗ[ℂ] E'))
    have h2 : LinearMap.range (D : E →ₗ[ℂ] E') ≠ ⊥ := by
      intro h
      apply hD
      ext v
      have : (D : E →ₗ[ℂ] E') v ∈ LinearMap.range (D : E →ₗ[ℂ] E') := ⟨v, rfl⟩
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this
    have h3 := Submodule.one_le_finrank_iff.2 h2
    omega
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (hE.trans hE'.symm)).2 hsurj
  exact ⟨hinj, hsurj⟩

/-- **A holomorphic map is a local homeomorphism at its non-critical points** (inverse function
theorem in the charts). -/
theorem b4cov_isLocalHomeomorphOn (hE : Module.finrank ℂ E = 1) (hE' : Module.finrank ℂ E' = 1)
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) :
    IsLocalHomeomorphOn f {x | mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x ≠ 0} := by
  have : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  have : FiniteDimensional ℂ E' := Module.finite_of_finrank_eq_succ hE'
  have := FiniteDimensional.complete ℂ E
  have := FiniteDimensional.complete ℂ E'
  refine IsLocalHomeomorphOn.mk f _ fun x hx ↦ ?_
  have hD : fderiv ℂ (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f) (extChartAt 𝓘(ℂ, E) x x) ≠ 0 :=
    fun h ↦ hx ((b4cov_mfderiv_eq_zero_iff f hf x x (mem_extChartAt_source x)
      (mem_extChartAt_source (f x))).2 h)
  have hbij := b4cov_bijective_of_ne_zero hE hE' _ hD
  let De : E ≃L[ℂ] E' := (LinearEquiv.ofBijective (fderiv ℂ (writtenInExtChartAt 𝓘(ℂ, E)
    𝓘(ℂ, E') x f) (extChartAt 𝓘(ℂ, E) x x) : E →ₗ[ℂ] E') hbij).toContinuousLinearEquiv
  have hstrict : HasStrictFDerivAt (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f)
      (De : E →L[ℂ] E') (extChartAt 𝓘(ℂ, E) x x) := by
    have := (b4cov_analyticOnNhd f hf x _ (b4cov_mem_good (E' := E') f x)).hasStrictFDerivAt
    have heq : (De : E →L[ℂ] E') = fderiv ℂ (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f)
        (extChartAt 𝓘(ℂ, E) x x) := by
      ext v; rfl
    rw [heq]
    exact this
  let G := hstrict.toOpenPartialHomeomorph
  have hG : (G : E → E') = writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f :=
    hstrict.toOpenPartialHomeomorph_coe
  have hW : IsOpen ((chartAt E x).source ∩ f ⁻¹' (chartAt E' (f x)).source) :=
    (chartAt E x).open_source.inter (hf.continuous.isOpen_preimage _ (chartAt E' (f x)).open_source)
  let e : OpenPartialHomeomorph C Y :=
    (((chartAt E x).trans G).trans (chartAt E' (f x)).symm).restrOpen _ hW
  have hφ : ∀ y, chartAt E x y = extChartAt 𝓘(ℂ, E) x y := fun y ↦ by
    simp [extChartAt_coe]
  have hφ' : ∀ y, chartAt E' (f x) y = extChartAt 𝓘(ℂ, E') (f x) y := fun y ↦ by
    simp [extChartAt_coe]
  have hψ : ∀ w, (chartAt E' (f x)).symm w = (extChartAt 𝓘(ℂ, E') (f x)).symm w := fun w ↦ by
    simp [extChartAt_coe_symm]
  refine ⟨e, ?_, fun y hy ↦ ?_⟩
  · refine ⟨⟨⟨mem_chart_source E x, ?_⟩, ?_⟩, mem_chart_source E x, ?_⟩
    · show chartAt E x x ∈ G.source
      rw [hφ]
      exact hstrict.mem_toOpenPartialHomeomorph_source
    · show G (chartAt E x x) ∈ (chartAt E' (f x)).target
      rw [hφ, hG, b4cov_written_apply, extChartAt_to_inv, ← hφ']
      exact (chartAt E' (f x)).map_source (mem_chart_source E' (f x))
    · exact mem_chart_source E' (f x)
  · have hy' := hy.2
    change f y = (chartAt E' (f x)).symm (G (chartAt E x y))
    rw [hφ, hG, hψ]
    exact b4cov_eq_symm_written f x y (by rw [extChartAt_source]; exact hy'.1)
      (by rw [extChartAt_source]; exact hy'.2)

/-- **Analyticity in arbitrary target charts**: `ψ_y ∘ f ∘ φ_x⁻¹` is analytic at chart points of
`x` whose image lies in the chart at `y`. -/
theorem b4cov_analyticAt_chart (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (x : C) (y : Y)
    (z : E) (hz : z ∈ (extChartAt 𝓘(ℂ, E) x).target)
    (hzy : f ((extChartAt 𝓘(ℂ, E) x).symm z) ∈ (extChartAt 𝓘(ℂ, E') y).source) :
    AnalyticAt ℂ (extChartAt 𝓘(ℂ, E') y ∘ f ∘ (extChartAt 𝓘(ℂ, E) x).symm) z := by
  have h1 : (extChartAt 𝓘(ℂ, E) x).symm z ∈ (chartAt E x).source := by
    rw [← extChartAt_source 𝓘(ℂ, E)]
    exact (extChartAt 𝓘(ℂ, E) x).map_target hz
  have h2 : f ((extChartAt 𝓘(ℂ, E) x).symm z) ∈ (chartAt E' y).source := by
    rw [← extChartAt_source 𝓘(ℂ, E')]
    exact hzy
  have := ((contMDiffAt_iff_of_mem_source h1 h2).1 (hf _)).2
  rw [(extChartAt 𝓘(ℂ, E) x).right_inv hz, modelWithCornersSelf_coe, range_id,
    contDiffWithinAt_univ] at this
  exact this.analyticAt

/-- **Identity theorem for holomorphic maps**: two holomorphic maps of a connected surface into a
Hausdorff surface that agree near one point agree everywhere. -/
theorem b4cov_eq_of_eventuallyEq [ConnectedSpace C] [T2Space Y] [CompleteSpace E']
    (f₁ f₂ : C → Y) (hf₁ : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f₁)
    (hf₂ : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f₂) (x₀ : C) (h₀ : f₁ =ᶠ[𝓝 x₀] f₂) : f₁ = f₂ := by
  let S : Set C := {x | f₁ =ᶠ[𝓝 x] f₂}
  have hSo : IsOpen S := isOpen_iff_mem_nhds.2 fun x hx ↦ hx.eventually_nhds
  have hSeq : S ⊆ {x | f₁ x = f₂ x} := fun x hx ↦ hx.self_of_nhds
  have hSc : IsClosed S := by
    refine isClosed_of_closure_subset fun x hx ↦ ?_
    have hfx : f₁ x = f₂ x :=
      closure_minimal hSeq (isClosed_eq hf₁.continuous hf₂.continuous) hx
    set φ := extChartAt 𝓘(ℂ, E) x
    set ψ := extChartAt 𝓘(ℂ, E') (f₁ x)
    let g₁ := ψ ∘ f₁ ∘ φ.symm
    let g₂ := ψ ∘ f₂ ∘ φ.symm
    let T : Set E := φ.target ∩ φ.symm ⁻¹' (f₁ ⁻¹' ψ.source ∩ f₂ ⁻¹' ψ.source)
    have hTo : IsOpen T :=
      (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x)
        ((hf₁.continuous.isOpen_preimage _ (isOpen_extChartAt_source _)).inter
          (hf₂.continuous.isOpen_preimage _ (isOpen_extChartAt_source _)))
    have hxs : x ∈ φ.source := mem_extChartAt_source x
    have hz0 : φ x ∈ T := by
      refine ⟨mem_extChartAt_target x, ?_⟩
      simp only [mem_preimage, mem_inter_iff, φ.left_inv hxs]
      exact ⟨mem_extChartAt_source _, hfx ▸ mem_extChartAt_source _⟩
    obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.1 hTo _ hz0
    have ha₁ : AnalyticOnNhd ℂ g₁ (Metric.ball (φ x) r) := fun z hz ↦
      b4cov_analyticAt_chart f₁ hf₁ x (f₁ x) z (hrT hz).1 (hrT hz).2.1
    have ha₂ : AnalyticOnNhd ℂ g₂ (Metric.ball (φ x) r) := fun z hz ↦
      b4cov_analyticAt_chart f₂ hf₂ x (f₁ x) z (hrT hz).1 (hrT hz).2.2
    let N : Set C := φ.source ∩ φ ⁻¹' Metric.ball (φ x) r ∩ f₁ ⁻¹' ψ.source ∩ f₂ ⁻¹' ψ.source
    have hN : N ∈ 𝓝 x := by
      refine inter_mem (inter_mem (inter_mem (extChartAt_source_mem_nhds x)
        ((continuousAt_extChartAt x).preimage_mem_nhds (Metric.ball_mem_nhds _ hr)))
        (hf₁.continuous.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds _))) ?_
      exact hf₂.continuous.continuousAt.preimage_mem_nhds (hfx ▸ extChartAt_source_mem_nhds _)
    have hrec : ∀ y ∈ N, ∀ (h : C → Y), h y ∈ ψ.source → h y = ψ.symm ((ψ ∘ h ∘ φ.symm) (φ y)) :=
      fun y hy h hh ↦ by
        simp only [Function.comp_apply, φ.left_inv hy.1.1.1, ψ.left_inv hh]
    obtain ⟨x', hx'N, hx'S⟩ := mem_closure_iff_nhds.1 hx N hN
    have hgc : g₁ =ᶠ[𝓝 (φ x')] g₂ := by
      have hc : ContinuousAt φ.symm (φ x') :=
        continuousAt_extChartAt_symm'' (φ.map_source hx'N.1.1.1)
      have := hc.preimage_mem_nhds (by rw [φ.left_inv hx'N.1.1.1]; exact hx'S)
      filter_upwards [this] with z hz
      exact congrArg ψ hz
    have hEq := ha₁.eqOn_of_preconnected_of_eventuallyEq ha₂ (convex_ball _ _).isPreconnected
      hx'N.1.1.2 hgc
    show ∀ᶠ y in 𝓝 x, f₁ y = f₂ y
    filter_upwards [hN] with y hy
    rw [hrec y hy f₁ hy.1.2, hrec y hy f₂ hy.2]
    exact congrArg ψ.symm (hEq hy.1.1.2)
  have hS : S = univ := IsClopen.eq_univ ⟨hSc, hSo⟩ ⟨x₀, h₀⟩
  funext x
  exact (hS ▸ (trivial : x ∈ univ) : x ∈ S).self_of_nhds

end Local

end HodgeLean.Foundations.Program
