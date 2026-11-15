import HodgeLean.Foundations.Program.HurwitzPrymRexFillTop

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-rex`: the group action and the map to `Y` are holomorphic

`G` acts on the filled surface (on `U`, and on the cosets over each puncture); in charts each
`g` is the identity on `U`-charts and a rotation `v ↦ ζʲ v` on puncture charts. The map to `Y` is
`φ ∘ φ⁻¹` on `U`-charts and `v ↦ φ_b b + κ'⁻¹ vᵉ` on puncture charts.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Topology Metric Set Complex Manifold HodgeLean.Foundations.Program.HurwitzPrymRexPunct
open scoped ContDiff

namespace HodgeLean.Foundations.Program

namespace HurwitzPrymRexFill

/-- **Holomorphy read in charts** (model spaces themselves). -/
theorem contMDiffAt_of_chart {E₁ E₂ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] {M M' : Type} [TopologicalSpace M]
    [ChartedSpace E₁ M] [TopologicalSpace M'] [ChartedSpace E₂ M'] {g : M → M'} {x : M}
    (hc : ContinuousAt g x) (F : E₁ → E₂) (hF : ContDiffAt ℂ ω F (chartAt E₁ x x))
    (heq : ∀ᶠ w in 𝓝 (chartAt E₁ x x), chartAt E₂ (g x) (g ((chartAt E₁ x).symm w)) = F w) :
    ContMDiffAt 𝓘(ℂ, E₁) 𝓘(ℂ, E₂) ω g x := by
  rw [contMDiffAt_iff]
  refine ⟨hc, ?_⟩
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp, range_id]
  exact (hF.congr_of_eventuallyEq (by filter_upwards [heq] with w hw; exact hw)).contDiffWithinAt

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y]
  [T2Space Y]
variable {B : Set Y} {G U : Type} [Group G] [TopologicalSpace U] [MulAction G U]
variable {p : U → {y : Y // y ∉ B}}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace Setup

variable (S : Setup E' p) (hp : IsQuotientCoveringMap p G) [Finite G] (κ : ℂ ≃L[ℂ] E)

instance : MulAction G (S.CC hp κ) := inferInstanceAs (MulAction G (U ⊕ S.Punct hp))

theorem smul_ι (g : G) (u : U) : g • S.ι hp κ u = S.ι hp κ (g • u) := rfl

theorem smul_ofP (g : G) (c : S.Punct hp) : g • S.ofP hp κ c = S.ofP hp κ (g • c) := rfl

theorem mem_target_aU {u : U} {w : E} (hw : w ∈ (chartAt E (S.ι hp κ u)).target) :
    κ.symm w ∈ (S.aU hp u).target := by
  rw [chartAt_target] at hw
  exact hw

theorem chartAt_ι_symm (u : U) (w : E) :
    (chartAt E (S.ι hp κ u)).symm w = S.ι hp κ ((S.aU hp u).symm (κ.symm w)) := rfl

theorem chartAt_ι_apply (u u' : U) :
    chartAt E (S.ι hp κ u) (S.ι hp κ u') = κ (S.κ' (chartAt E' (p u).1 (p u').1)) := by
  rw [chartAt_apply]
  change κ (S.aU hp u u') = _
  rw [aU_apply]

/-- **The map to `Y` is holomorphic.** -/
theorem contMDiff_f : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω (S.f hp κ) := by
  intro x
  rcases x with u | c
  · refine contMDiffAt_of_chart ((S.continuous_f hp κ).continuousAt)
      (fun w ↦ S.κ'.symm (κ.symm w)) (S.κ'.symm.contDiff.comp κ.symm.contDiff).contDiffAt ?_
    have hx : chartAt E (S.ι hp κ u) (S.ι hp κ u) ∈ (chartAt E (S.ι hp κ u)).target :=
      (chartAt E _).map_source (_root_.mem_chart_source E _)
    filter_upwards [(chartAt E (S.ι hp κ u)).open_target.mem_nhds hx] with w hw
    change chartAt E' (p u).1 (p ((S.aU hp u).symm (κ.symm w))).1 = _
    rw [S.p_aU_symm hp (S.mem_target_aU hp κ hw),
      (chartAt E' (p u).1).right_inv (S.aU_target_mem hp (S.mem_target_aU hp κ hw))]
  · set b := c.1
    refine contMDiffAt_of_chart ((S.continuous_f hp κ).continuousAt)
      (fun w ↦ chartAt E' b.1 b.1 + S.κ'.symm ((κ.symm w) ^ (S.D hp b).e))
      (contDiff_const.add (S.κ'.symm.contDiff.comp
        ((contDiff_id.pow _).comp κ.symm.contDiff))).contDiffAt ?_
    have hx : chartAt E (S.ofP hp κ c) (S.ofP hp κ c) ∈ (chartAt E (S.ofP hp κ c)).target :=
      (chartAt E _).map_source (_root_.mem_chart_source E _)
    filter_upwards [(chartAt E (S.ofP hp κ c)).open_target.mem_nhds hx] with w hw
    rw [chartAt_target] at hw
    have hsrc := (S.pChart hp c).map_target hw
    have h1 := S.f_eq_on_pChart hp κ c hsrc
    rw [(S.pChart hp c).right_inv hw] at h1
    change chartAt E' b.1 (S.f hp κ ((S.pChart hp c).symm (κ.symm w))) = _
    rw [h1]
    have hz : (κ.symm w) ^ (S.D hp b).e ∈ ball (0 : ℂ) (S.r b) :=
      mem_ball_zero_iff.2 (by rw [norm_pow]; exact hw)
    simp only [ξY]
    rw [(chartAt E' b.1).right_inv (S.hTgt b hz)]

omit [IsManifold 𝓘(ℂ, E') ω Y] in
/-- The rotation exponent of `g` at a new point `c`. -/
theorem exists_rot (g : G) (c : S.Punct hp) :
    ∃ j : ℤ, g * c.2.out = (g • c).2.out * (S.D hp c.1).h ^ j := by
  have hmem : (g • c).2.out⁻¹ * (g * c.2.out) ∈ Subgroup.zpowers (S.D hp c.1).h := by
    have h1 : ((g • c.2).out : G ⧸ Subgroup.zpowers (S.D hp c.1).h) = g • c.2 :=
      QuotientGroup.out_eq' (g • c.2)
    have h2 : ((g * c.2.out : G) : G ⧸ Subgroup.zpowers (S.D hp c.1).h) = g • c.2 := by
      have := MulAction.Quotient.coe_smul_out (H := Subgroup.zpowers (S.D hp c.1).h) g c.2
      rwa [smul_eq_mul] at this
    rw [← QuotientGroup.eq]
    exact h1.trans h2.symm
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hmem
  exact ⟨j, by rw [hj, mul_inv_cancel_left]⟩

omit [IsManifold 𝓘(ℂ, E') ω Y] in
theorem smul_pChart_symm (g : G) (c : S.Punct hp) {j : ℤ}
    (hj : g * c.2.out = (g • c).2.out * (S.D hp c.1).h ^ j) {v : ℂ}
    (hv : v ∈ (S.pChart hp c).target) :
    (g • ((S.pChart hp c).symm v : S.CC hp κ)) =
      (S.pChart hp (g • c)).symm ((S.D hp c.1).ζ ^ j * v) := by
  by_cases h0 : v = 0
  · subst h0
    rw [mul_zero, S.pChart_symm_zero hp, S.pChart_symm_zero hp]
    rfl
  · have hvD : v ∈ (S.D hp c.1).Dom := ⟨h0, hv⟩
    have hne : (S.D hp c.1).ζ ^ j * v ≠ 0 := mul_ne_zero (zpow_ne_zero _ (exp_ne_zero _)) h0
    rw [S.pChart_symm_of_ne hp h0, S.pChart_symm_of_ne hp hne]
    change Sum.inl (g • (S.D hp c.1).M c.2.out v) = Sum.inl ((S.D hp c.1).M (g • c).2.out _)
    congr 1
    rw [Datum.M, smul_smul, ← Datum.M, hj, Datum.M_mul_zpow hp _ hvD, mul_comm]

/-- **Each `g` acts holomorphically.** -/
theorem contMDiff_smul (g : G) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : S.CC hp κ ↦ g • x) := by
  have := hp.toContinuousConstSMul
  intro x
  rcases x with u | c
  · have hc : ContinuousAt (fun x : S.CC hp κ ↦ g • x) (S.ι hp κ u) := by
      rw [← (S.isOpenEmbedding_ι hp κ).continuousAt_iff]
      exact ((S.continuous_ι hp κ).comp (continuous_const_smul g)).continuousAt
    refine contMDiffAt_of_chart hc id contDiff_id.contDiffAt ?_
    have hx : chartAt E (S.ι hp κ u) (S.ι hp κ u) ∈ (chartAt E (S.ι hp κ u)).target :=
      (chartAt E _).map_source (_root_.mem_chart_source E _)
    filter_upwards [(chartAt E (S.ι hp κ u)).open_target.mem_nhds hx] with w hw
    have hw' := S.mem_target_aU hp κ hw
    change chartAt E (S.ι hp κ (g • u)) (S.ι hp κ (g • (S.aU hp u).symm (κ.symm w))) = w
    rw [chartAt_ι_apply, Datum.p_smul hp, Datum.p_smul hp, S.p_aU_symm hp hw',
      (chartAt E' (p u).1).right_inv (S.aU_target_mem hp hw')]
    simp
  · obtain ⟨j, hj⟩ := S.exists_rot hp g c
    set e := chartAt E (S.ofP hp κ c)
    set e' := chartAt E (S.ofP hp κ (g • c))
    have hx : e (S.ofP hp κ c) ∈ e.target := e.map_source (_root_.mem_chart_source E _)
    have hnorm : ∀ v : ℂ, ‖(S.D hp c.1).ζ ^ j * v‖ = ‖v‖ := fun v ↦ by
      rw [norm_mul, Datum.norm_ζ_pow, one_mul]
    -- the formula on the chart target
    have key : ∀ w ∈ e.target, g • e.symm w = e'.symm (κ ((S.D hp c.1).ζ ^ j * κ.symm w)) ∧
        κ ((S.D hp c.1).ζ ^ j * κ.symm w) ∈ e'.target := by
      intro w hw
      rw [chartAt_target] at hw
      refine ⟨?_, ?_⟩
      · rw [chartAt_symm_apply, chartAt_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
        exact S.smul_pChart_symm hp g c hj hw
      · rw [chartAt_target]
        change κ.symm (κ _) ∈ (S.pChart hp (g • c)).target
        rw [ContinuousLinearEquiv.symm_apply_apply]
        change ‖(S.D hp c.1).ζ ^ j * κ.symm w‖ ^ (S.D hp c.1).e < S.r c.1
        rw [hnorm]
        exact hw
    have hlin : ContDiff ℂ ω (fun w : E ↦ κ ((S.D hp c.1).ζ ^ j * κ.symm w)) :=
      κ.contDiff.comp ((contDiff_const.mul contDiff_id).comp κ.symm.contDiff)
    have hc : ContinuousAt (fun x : S.CC hp κ ↦ g • x) (S.ofP hp κ c) := by
      have hsrc : e.source ∈ 𝓝 (S.ofP hp κ c) :=
        e.open_source.mem_nhds (_root_.mem_chart_source E _)
      have h0 : κ ((S.D hp c.1).ζ ^ j * κ.symm (e (S.ofP hp κ c))) = e' (S.ofP hp κ (g • c)) := by
        rw [chartAt_ofP_self, chartAt_ofP_self, map_zero, mul_zero, map_zero]
      have h1 : ContinuousAt e'.symm (κ ((S.D hp c.1).ζ ^ j * κ.symm (e (S.ofP hp κ c)))) := by
        rw [h0]
        exact e'.continuousAt_symm (e'.map_source (_root_.mem_chart_source E _))
      have h2 : ContinuousAt (fun x ↦ e'.symm (κ ((S.D hp c.1).ζ ^ j * κ.symm (e x))))
          (S.ofP hp κ c) :=
        ContinuousAt.comp (f := fun x ↦ κ ((S.D hp c.1).ζ ^ j * κ.symm (e x))) h1
          (hlin.continuous.continuousAt.comp (e.continuousAt (_root_.mem_chart_source E _)))
      refine h2.congr ?_
      filter_upwards [hsrc] with y hy
      have := (key (e y) (e.map_source hy)).1
      rw [e.left_inv hy] at this
      exact this.symm
    refine contMDiffAt_of_chart hc _ hlin.contDiffAt ?_
    filter_upwards [e.open_target.mem_nhds hx] with w hw
    obtain ⟨h1, h2⟩ := key w hw
    change e' (g • e.symm w) = _
    rw [h1, e'.right_inv h2]

omit [IsManifold 𝓘(ℂ, E') ω Y] [T2Space Y] in
/-- **`f` is `G`-invariant.** -/
theorem f_smul (g : G) (x : S.CC hp κ) : S.f hp κ (g • x) = S.f hp κ x := by
  · rcases x with u | c
    · change (p (g • u)).1 = (p u).1
      rw [Datum.p_smul hp]
    · rfl

omit [IsManifold 𝓘(ℂ, E') ω Y] [T2Space Y] in
/-- **`G` is transitive on the fibres of `f`.** -/
theorem exists_smul_of_f_eq {x x' : S.CC hp κ} (hxx : S.f hp κ x = S.f hp κ x') :
    ∃ g : G, g • x = x' := by
  · rcases x with u | ⟨b, q⟩ <;> rcases x' with u' | ⟨b', q'⟩
    · have hpu : p u = p u' := Subtype.ext hxx
      obtain ⟨g, hg⟩ := hp.apply_eq_iff_mem_orbit.1 hpu.symm
      exact ⟨g, congrArg Sum.inl hg⟩
    · have h' : (p u).1 = b'.1 := hxx
      exact absurd (h' ▸ b'.2) (p u).2
    · have h' : b.1 = (p u').1 := hxx
      exact absurd (h' ▸ b.2) (p u').2
    · have hb : b = b' := Subtype.ext hxx
      subst hb
      refine ⟨q'.out * q.out⁻¹, ?_⟩
      change (Sum.inr ⟨b, (q'.out * q.out⁻¹) • q⟩ : U ⊕ S.Punct hp) = Sum.inr ⟨b, q'⟩
      congr 2
      have h1 : (q'.out * q.out⁻¹) • q =
          ((q'.out * q.out⁻¹ * q.out : G) : G ⧸ Subgroup.zpowers (S.D hp b).h) := by
        rw [← MulAction.Quotient.coe_smul_out, smul_eq_mul]
      rw [h1, inv_mul_cancel_right, QuotientGroup.out_eq']

end Setup

end HurwitzPrymRexFill

end HodgeLean.Foundations.Program
