import HodgeLean.Foundations.Program.HurwitzPrymRexFillCore

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-rex`: the filled surface is a Riemann surface

The chart transitions of the filled surface are analytic: between two charts of `U` they are
transitions of `Y`; from a new point to `U` they are `v ↦ κ' φ (ξ_b (vᵉ))`; from `U` to a new point
they are branches of `(ψ_b ∘ φ⁻¹)^{1/e}`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Topology Metric Set Complex Manifold HodgeLean.Foundations.Program.HurwitzPrymRexPunct
open scoped ContDiff

namespace HodgeLean.Foundations.Program

namespace HurwitzPrymRexFill

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y]

/-- **Chart transitions of `Y` are analytic.** -/
theorem Y_transition_contDiffOn (y₁ y₂ : Y) :
    ContDiffOn ℂ ω ((chartAt E' y₁).symm.trans (chartAt E' y₂))
      ((chartAt E' y₁).symm.trans (chartAt E' y₂)).source := by
  have h := HasGroupoid.compatible (G := contDiffGroupoid ω 𝓘(ℂ, E'))
    (chart_mem_atlas E' y₁) (chart_mem_atlas E' y₂)
  have h1 := (mem_groupoid_of_pregroupoid.1 h).1
  simpa [contDiffPregroupoid] using h1

variable {B : Set Y} {G U : Type} [Group G] [TopologicalSpace U] [MulAction G U]
variable {p : U → {y : Y // y ∉ B}}

namespace Setup

variable (S : Setup E' p) (hp : IsQuotientCoveringMap p G) [Finite G]

theorem aU_source_mem {u w : U} (hw : w ∈ (S.aU hp u).source) :
    (p w).1 ∈ (chartAt E' (p u).1).source := by
  rw [aU, OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
    OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
    OpenPartialHomeomorph.trans_source, mem_inter_iff] at hw
  have h := hw.2.2.1
  rw [valHom_apply, ← σ_eq hp u] at h
  exact h

theorem aU_symm_apply {u : U} {z : ℂ} (hz : z ∈ (S.aU hp u).target) :
    chartAt E' (p u).1 (p ((S.aU hp u).symm z)).1 = S.κ'.symm z := by
  have h2 := (S.aU hp u).right_inv hz
  rw [aU_apply] at h2
  rw [eq_comm, ContinuousLinearEquiv.symm_apply_eq]
  exact h2.symm

theorem p_aU_symm {u : U} {z : ℂ} (hz : z ∈ (S.aU hp u).target) :
    (p ((S.aU hp u).symm z)).1 = (chartAt E' (p u).1).symm (S.κ'.symm z) := by
  rw [← S.aU_symm_apply hp hz,
    (chartAt E' (p u).1).left_inv (S.aU_source_mem hp ((S.aU hp u).map_target hz))]

theorem aU_target_mem {u : U} {z : ℂ} (hz : z ∈ (S.aU hp u).target) :
    S.κ'.symm z ∈ (chartAt E' (p u).1).target := by
  rw [← S.aU_symm_apply hp hz]
  exact (chartAt E' (p u).1).map_source (S.aU_source_mem hp ((S.aU hp u).map_target hz))

theorem contDiffOn_AA (u u' : U) :
    ContDiffOn ℂ ω ((S.chart hp (Sum.inl u)).symm.trans (S.chart hp (Sum.inl u')))
      ((S.chart hp (Sum.inl u)).symm.trans (S.chart hp (Sum.inl u'))).source := by
  simp only [chart]
  rw [liftL_symm_trans]
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = (chartAt E' (p u).1).symm.trans (chartAt E' (p u').1) := ⟨_, rfl⟩
  have hF : ContDiffOn ℂ ω (fun z ↦ S.κ' (Φ (S.κ'.symm z))) (S.κ'.symm ⁻¹' Φ.source) := by
    subst hΦ
    exact
    S.κ'.contDiff.comp_contDiffOn ((Y_transition_contDiffOn _ _).comp
      S.κ'.symm.contDiff.contDiffOn fun z hz ↦ hz)
  refine (hF.mono ?_).congr ?_
  · rintro z ⟨hz, hz'⟩
    subst hΦ
    have hz1 : z ∈ (S.aU hp u).target := hz
    have hz2 : (S.aU hp u).symm z ∈ (S.aU hp u').source := hz'
    have e2 := S.aU_source_mem hp hz2
    rw [S.p_aU_symm hp hz1] at e2
    exact ⟨S.aU_target_mem hp hz1, e2⟩
  · rintro z ⟨hz, hz'⟩
    subst hΦ
    have hz1 : z ∈ (S.aU hp u).target := hz
    have e1 := S.p_aU_symm hp hz1
    change S.aU hp u' ((S.aU hp u).symm z) = _
    rw [aU_apply, e1]
    rfl

theorem contDiffOn_PA (c : S.Punct hp) (u : U) :
    ContDiffOn ℂ ω ((S.chart hp (Sum.inr c)).symm.trans (S.chart hp (Sum.inl u)))
      ((S.chart hp (Sum.inr c)).symm.trans (S.chart hp (Sum.inl u))).source := by
  rw [source_PA]
  set b := c.1
  set Φ := (chartAt E' b.1).symm.trans (chartAt E' (p u).1)
  set inner : ℂ → E' := fun v ↦ chartAt E' b.1 b.1 + S.κ'.symm (v ^ (S.D hp b).e)
  have hinner : ContDiff ℂ ω inner :=
    contDiff_const.add (S.κ'.symm.contDiff.comp (contDiff_id.pow _))
  have hF : ContDiffOn ℂ ω (fun v ↦ S.κ' (Φ (inner v))) (inner ⁻¹' Φ.source) :=
    S.κ'.contDiff.comp_contDiffOn ((Y_transition_contDiffOn _ _).comp hinner.contDiffOn
      fun v hv ↦ hv)
  refine (hF.mono ?_).congr ?_
  · rintro v ⟨hv, hv'⟩
    have hball : v ^ (S.D hp b).e ∈ ball (0 : ℂ) (S.r b) :=
      mem_ball_zero_iff.2 (by rw [norm_pow]; exact hv.2)
    refine ⟨S.hTgt b hball, ?_⟩
    change ξY S.κ' b.1 (v ^ (S.D hp b).e) ∈ (chartAt E' (p u).1).source
    rw [← S.val_p_M hp b c.2.out hv]
    exact S.aU_source_mem hp hv'
  · rintro v ⟨hv, hv'⟩
    change Sum.elim (S.aU hp u) (fun _ ↦ 0) ((S.pChart hp c).symm v) = _
    rw [pChart_symm_of_ne S hp hv.1]
    change S.aU hp u ((S.D hp b).M c.2.out v) = _
    rw [aU_apply, S.val_p_M hp b c.2.out hv]
    rfl

omit [IsManifold 𝓘(ℂ, E') ω Y] in
theorem analyticAt_R (b : B) {v₀ : ℂ} (hv₀ : v₀ ≠ 0) :
    AnalyticAt ℂ ((S.D hp b).R v₀) (v₀ ^ (S.D hp b).e) := by
  have h1 : (v₀ ^ (S.D hp b).e / v₀ ^ (S.D hp b).e) ∈ slitPlane := by
    rw [div_self (pow_ne_zero _ hv₀)]; exact one_mem_slitPlane
  have h2 : AnalyticAt ℂ (fun w : ℂ ↦ (w / v₀ ^ (S.D hp b).e) ^ (((S.D hp b).e : ℂ)⁻¹))
      (v₀ ^ (S.D hp b).e) :=
    (analyticAt_id.div_const (c := v₀ ^ (S.D hp b).e)).cpow analyticAt_const h1
  exact analyticAt_const.mul h2

theorem contDiffOn_AP (u : U) (c : S.Punct hp) :
    ContDiffOn ℂ ω ((S.chart hp (Sum.inl u)).symm.trans (S.chart hp (Sum.inr c)))
      ((S.chart hp (Sum.inl u)).symm.trans (S.chart hp (Sum.inr c))).source := by
  have hopen := (S.transition_AP hp u c).1
  intro z₀ hz₀
  refine ContDiffAt.contDiffWithinAt ?_
  have hz₀' := hz₀
  rw [source_AP] at hz₀'
  obtain ⟨hz₀t, v₀, hv₀, hzv⟩ := hz₀'
  have hsymm : ContinuousAt (S.aU hp u).symm z₀ :=
    (S.aU hp u).continuousOn_symm.continuousAt ((S.aU hp u).open_target.mem_nhds hz₀t)
  -- the explicit formula near `z₀`
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ, Ψ = (chartAt E' (p u).1).symm.trans (chartAt E' c.1.1) := ⟨_, rfl⟩
  have hu₀ : (p ((S.aU hp u).symm z₀)).1 = ξY S.κ' c.1.1 (v₀ ^ (S.D hp c.1).e) := by
    rw [← hzv, S.val_p_M hp c.1 c.2.out hv₀]
  have hball : v₀ ^ (S.D hp c.1).e ∈ ball (0 : ℂ) (S.r c.1) :=
    mem_ball_zero_iff.2 (by rw [norm_pow]; exact hv₀.2)
  have hΨsrc : S.κ'.symm z₀ ∈ Ψ.source := by
    subst hΨ
    refine ⟨S.aU_target_mem hp hz₀t, ?_⟩
    change (chartAt E' (p u).1).symm (S.κ'.symm z₀) ∈ (chartAt E' c.1.1).source
    rw [← S.p_aU_symm hp hz₀t, hu₀]
    exact ξY_mem_source (S.hTgt c.1 hball)
  have hΨc : ContDiffAt ℂ ω Ψ (S.κ'.symm z₀) := by
    subst hΨ
    exact (Y_transition_contDiffOn _ _).contDiffAt
      (((chartAt E' (p u).1).symm.trans (chartAt E' c.1.1)).open_source.mem_nhds hΨsrc)
  have hval : S.κ' (Ψ (S.κ'.symm z₀) - chartAt E' c.1.1 c.1.1) = v₀ ^ (S.D hp c.1).e := by
    subst hΨ
    change S.κ' (chartAt E' c.1.1 ((chartAt E' (p u).1).symm (S.κ'.symm z₀)) -
      chartAt E' c.1.1 c.1.1) = _
    rw [← S.p_aU_symm hp hz₀t, hu₀]
    exact ψY_ξY (S.hTgt c.1 hball)
  have hinner : ContDiffAt ℂ ω (fun z ↦ S.κ' (Ψ (S.κ'.symm z) - chartAt E' c.1.1 c.1.1)) z₀ :=
    S.κ'.contDiff.contDiffAt.comp _ ((hΨc.comp _ S.κ'.symm.contDiff.contDiffAt).sub
      contDiffAt_const)
  have hR := (S.analyticAt_R hp c.1 hv₀.1).contDiffAt (n := ω)
  rw [← hval] at hR
  have hH := hR.comp z₀ hinner
  refine hH.congr_of_eventuallyEq ?_
  have hev := Datum.eventually_M_R hp (D := S.D hp c.1) c.2.out hv₀
  rw [hzv] at hev
  filter_upwards [hsymm.preimage_mem_nhds hev, (S.aU hp u).open_target.mem_nhds hz₀t] with z hz hzt
  obtain ⟨hzD, hzM⟩ := hz
  change (S.pChart hp c) (Sum.inl ((S.aU hp u).symm z)) = _
  conv_lhs => rw [← hzM]
  rw [S.pChart_inl_M hp c hzD]
  subst hΨ
  change _ = (S.D hp c.1).R v₀ (S.κ' (chartAt E' c.1.1 ((chartAt E' (p u).1).symm (S.κ'.symm z)) -
    chartAt E' c.1.1 c.1.1))
  rw [← S.p_aU_symm hp hzt]
  rfl

omit [IsManifold 𝓘(ℂ, E') ω Y] in
theorem contDiffOn_PP (c c' : S.Punct hp) :
    ContDiffOn ℂ ω ((S.chart hp (Sum.inr c)).symm.trans (S.chart hp (Sum.inr c')))
      ((S.chart hp (Sum.inr c)).symm.trans (S.chart hp (Sum.inr c'))).source := by
  simp only [chart]
  by_cases hcc : c = c'
  · subst hcc
    exact contDiffOn_id.congr fun v hv ↦ (S.pChart hp c).right_inv hv.1
  · have hsrc : ((S.pChart hp c).symm.trans (S.pChart hp c')).source = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro v ⟨hv, hv'⟩
      exact Set.disjoint_left.1 (S.pChart_source_disjoint hp hcc)
        ((S.pChart hp c).map_target hv) hv'
    rw [hsrc]
    exact contDiffOn_empty

theorem transition_contDiffOn (x y : S.C hp) :
    ContDiffOn ℂ ω ((S.chart hp x).symm.trans (S.chart hp y))
      ((S.chart hp x).symm.trans (S.chart hp y)).source := by
  rcases x with u | c <;> rcases y with u' | c'
  · exact S.contDiffOn_AA hp u u'
  · exact S.contDiffOn_AP hp u c'
  · exact S.contDiffOn_PA hp c u'
  · exact S.contDiffOn_PP hp c c'

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **The filled surface is a Riemann surface.** -/
theorem isManifold (κ : ℂ ≃L[ℂ] E) :
    letI := (S.core hp κ).toTopologicalSpace
    letI := (S.core hp κ).toChartedSpace
    IsManifold 𝓘(ℂ, E) ω (S.C hp) := by
  letI := (S.core hp κ).toTopologicalSpace
  letI := (S.core hp κ).toChartedSpace
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨e₀, he₀⟩ := Set.mem_iUnion.1 he
  obtain ⟨he₀a, he₀s⟩ := Set.mem_iUnion.1 he₀
  rw [Set.mem_singleton_iff] at he₀s
  subst he₀s
  obtain ⟨e₁, he₁⟩ := Set.mem_iUnion.1 he'
  obtain ⟨he₁a, he₁s⟩ := Set.mem_iUnion.1 he₁
  rw [Set.mem_singleton_iff] at he₁s
  subst he₁s
  obtain ⟨x, rfl⟩ := he₀a
  obtain ⟨y, rfl⟩ := he₁a
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, preimage_id_eq, id_eq, range_id, inter_univ]
  change ContDiffOn ℂ ω (((S.chart hp x).trans (κPE κ)).symm.trans ((S.chart hp y).trans (κPE κ)))
    (((S.chart hp x).trans (κPE κ)).symm.trans ((S.chart hp y).trans (κPE κ))).source
  rw [trans_κ_source]
  exact κ.contDiff.comp_contDiffOn ((S.transition_contDiffOn hp x y).comp
    κ.symm.contDiff.contDiffOn fun w hw ↦ hw)

end Setup

end HurwitzPrymRexFill

end HodgeLean.Foundations.Program
