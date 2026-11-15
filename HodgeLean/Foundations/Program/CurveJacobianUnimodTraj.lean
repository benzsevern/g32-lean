import HodgeLean.Foundations.Program.CurveJacobianUnimodFlat

/-! # Track B3, lane Unimod: vertical trajectories of a holomorphic form

A curve `τ : ℝ → C` is **vertical** for `θ` (`b3Unimod_Vertical`) if near every parameter it is,
in some flat chart `F`, the vertical line `F (τ s) = F (τ t) - i (s - t)`. Then
* the same holds in every flat chart through `τ t` (`b3Unimod_Vertical.eventually`), `τ` is `C¹`
  and `θ(τ, τ') = -i`;
* two vertical curves through a common point agree up to a shift of the parameter
  (`b3Unimod_Vertical.shift_eq`), and a vertical curve follows the vertical line of a flat chart
  as long as the line stays in the target (`b3Unimod_Vertical.line`);
* a vertical curve that returns to a point is periodic, with a least period on which it is
  injective (`b3Unimod_Vertical.exists_minPeriod`);
* `b3Unimod_exists_vertical`: given flat charts of a uniform radius `ρ` at the points of a set `K`
  that is invariant under the vertical lines of length `< ρ`, every point of `K` lies on a vertical
  curve in `K`: step by `ρ / 3` from chart to chart, forwards and backwards.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
  {hE : Module.finrank ℂ E = 1} {θ : b3_HolForm E C}

variable (hE θ) in
/-- **A vertical curve** of `θ`: locally a vertical line `s ↦ F⁻¹ (F (τ t) - i (s - t))` in a flat
chart. -/
def b3Unimod_Vertical (τ : ℝ → C) : Prop :=
  ∀ t, ∃ Fl : b3Unimod_Flat hE θ, τ t ∈ Fl.F.source ∧
    ∀ᶠ s in 𝓝 t, τ s ∈ Fl.F.source ∧ Fl.F (τ s) = Fl.F (τ t) - Complex.I * ((s - t : ℝ) : ℂ)

namespace b3Unimod_Vertical

variable {τ : ℝ → C} (hτ : b3Unimod_Vertical hE θ τ)
include hτ

theorem eventuallyEq (t : ℝ) : ∃ Fl : b3Unimod_Flat hE θ, τ t ∈ Fl.F.source ∧
    τ =ᶠ[𝓝 t] fun s ↦ Fl.F.symm (Fl.F (τ t) - Complex.I * ((s - t : ℝ) : ℂ)) := by
  obtain ⟨Fl, ht, hev⟩ := hτ t
  refine ⟨Fl, ht, ?_⟩
  filter_upwards [hev] with s ⟨hs, he⟩
  rw [← he, Fl.F.left_inv hs]

theorem continuousAt (t : ℝ) : ContinuousAt τ t := by
  obtain ⟨Fl, ht, hev⟩ := hτ.eventuallyEq t
  refine ContinuousAt.congr ?_ hev.symm
  refine (Fl.F.continuousAt_symm ?_).comp (by fun_prop)
  simpa using Fl.F.map_source ht

theorem continuous : Continuous τ := continuous_iff_continuousAt.2 hτ.continuousAt

theorem contMDiff : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 τ := fun t ↦ by
  obtain ⟨Fl, ht, hev⟩ := hτ.eventuallyEq t
  have hℓ : ContDiff ℝ 1 fun s : ℝ ↦ Fl.F (τ t) - Complex.I * ((s - t : ℝ) : ℂ) :=
    contDiff_const.sub (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_id.sub contDiff_const)))
  refine (Fl.contMDiffAt_symm_comp hℓ.contDiffAt ?_).congr_of_eventuallyEq hev
  simpa using Fl.F.map_source ht

/-- **A vertical curve is vertical in every flat chart.** -/
theorem eventually (Fl' : b3Unimod_Flat hE θ) {t : ℝ} (ht : τ t ∈ Fl'.F.source) :
    ∀ᶠ s in 𝓝 t, τ s ∈ Fl'.F.source ∧
      Fl'.F (τ s) = Fl'.F (τ t) - Complex.I * ((s - t : ℝ) : ℂ) := by
  obtain ⟨Fl, hFt, hev⟩ := hτ t
  have h1 := (hτ.continuousAt t).eventually (Fl.eventually_sub Fl' hFt ht)
  filter_upwards [h1, hev] with s ⟨_, h2, h3⟩ ⟨_, h4⟩
  refine ⟨h2, ?_⟩
  linear_combination h3 + h4

/-- `θ(τ, τ') = -i` along a vertical curve. -/
theorem integrand (t : ℝ) : θ.1 ⟨τ t, b3_velocity E C τ t⟩ = -Complex.I := by
  obtain ⟨Fl, ht, hev⟩ := hτ t
  have h1 := Fl.hasDeriv τ t (hτ.contMDiff t) ht
  have h2 : HasDerivAt (fun s : ℝ ↦ Fl.F (τ t) - Complex.I * ((s - t : ℝ) : ℂ)) (-Complex.I) t := by
    have := ((((hasDerivAt_id t).sub_const t).ofReal_comp).const_mul Complex.I).const_sub
      (Fl.F (τ t))
    simpa using this
  have h3 : (fun s ↦ Fl.F (τ s)) =ᶠ[𝓝 t] fun s : ℝ ↦ Fl.F (τ t) - Complex.I * ((s - t : ℝ) : ℂ) :=
    hev.mono fun s hs ↦ hs.2
  exact h1.unique (h2.congr_of_eventuallyEq h3)

/-- A shifted vertical curve is vertical. -/
theorem comp_add (a : ℝ) : b3Unimod_Vertical hE θ fun s ↦ τ (s + a) := by
  intro t
  obtain ⟨Fl, ht, hev⟩ := hτ (t + a)
  refine ⟨Fl, ht, ?_⟩
  have hc : Tendsto (fun s : ℝ ↦ s + a) (𝓝 t) (𝓝 (t + a)) :=
    (continuous_id.add continuous_const).tendsto t
  filter_upwards [hc.eventually hev] with s ⟨hs, he⟩
  refine ⟨hs, ?_⟩
  rw [he]
  congr 3
  ring

/-- **Uniqueness of vertical curves.** -/
theorem shift_eq [T2Space C] {τ' : ℝ → C} (hτ' : b3Unimod_Vertical hE θ τ') {t t' : ℝ}
    (h : τ t = τ' t') : ∀ s, τ (t + s) = τ' (t' + s) := by
  set A := {s : ℝ | τ (t + s) = τ' (t' + s)}
  have hAc : IsClosed A := isClosed_eq (hτ.continuous.comp (continuous_const.add continuous_id))
    (hτ'.continuous.comp (continuous_const.add continuous_id))
  have hAo : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    obtain ⟨Fl, hFs, hev⟩ := hτ (t + s)
    have hs' : τ' (t' + s) ∈ Fl.F.source := hs ▸ hFs
    have hev' := hτ'.eventually Fl hs'
    have hc : Tendsto (fun s' : ℝ ↦ t + s') (𝓝 s) (𝓝 (t + s)) :=
      (continuous_const.add continuous_id).tendsto s
    have hc' : Tendsto (fun s' : ℝ ↦ t' + s') (𝓝 s) (𝓝 (t' + s)) :=
      (continuous_const.add continuous_id).tendsto s
    filter_upwards [hc.eventually hev, hc'.eventually hev'] with s' ⟨h1, h2⟩ ⟨h3, h4⟩
    refine Fl.F.injOn h1 h3 ?_
    rw [h2, h4, ← hs]
    congr 3
    ring
  have := (isClopen_iff.1 ⟨hAc, hAo⟩).resolve_left (Set.nonempty_iff_ne_empty.1
    ⟨0, by simpa [A] using h⟩)
  intro s
  have hs : s ∈ A := by rw [this]; trivial
  exact hs

/-- **A vertical curve follows the vertical lines of a flat chart.** -/
theorem line [T2Space C] (Fl : b3Unimod_Flat hE θ) {t₀ : ℝ} {w₀ : ℂ} {R : ℝ}
    (hR : Metric.ball w₀ R ⊆ Fl.F.target) (h₀ : τ t₀ = Fl.F.symm w₀) {s : ℝ} (hs : |s| < R) :
    τ (t₀ + s) = Fl.F.symm (w₀ - Complex.I * (s : ℂ)) := by
  have hR0 : 0 < R := lt_of_le_of_lt (abs_nonneg s) hs
  have hmem : ∀ s' : ℝ, |s'| < R → w₀ - Complex.I * (s' : ℂ) ∈ Metric.ball w₀ R := by
    intro s' hs'
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I,
      one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact hs'
  set I := Ioo (-R) R
  have hI : ∀ s' ∈ I, |s'| < R := fun s' hs' ↦ abs_lt.2 hs'
  set A := {s' : ℝ | s' ∈ I ∧ τ (t₀ + s') = Fl.F.symm (w₀ - Complex.I * (s' : ℂ))}
  have hc2 : ∀ s' ∈ I, ContinuousAt (fun s' : ℝ ↦ Fl.F.symm (w₀ - Complex.I * (s' : ℂ))) s' :=
    fun s' hs' ↦ (Fl.F.continuousAt_symm (hR (hmem s' (hI s' hs')))).comp
      (f := fun s' : ℝ ↦ w₀ - Complex.I * (s' : ℂ)) (by fun_prop)
  have hc1 : Continuous fun s' : ℝ ↦ τ (t₀ + s') :=
    hτ.continuous.comp (continuous_const.add continuous_id)
  have hAo : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    rintro s' ⟨hs', he⟩
    have hsrc : τ (t₀ + s') ∈ Fl.F.source := he ▸ Fl.F.map_target (hR (hmem s' (hI s' hs')))
    have hF : Fl.F (τ (t₀ + s')) = w₀ - Complex.I * (s' : ℂ) := by
      rw [he]; exact Fl.F.right_inv (hR (hmem s' (hI s' hs')))
    have hc : Tendsto (fun s'' : ℝ ↦ t₀ + s'') (𝓝 s') (𝓝 (t₀ + s')) :=
      (continuous_const.add continuous_id).tendsto s'
    filter_upwards [hc.eventually (hτ.eventually Fl hsrc), isOpen_Ioo.mem_nhds hs'] with
      s'' ⟨h1, h2⟩ hs''
    refine ⟨hs'', ?_⟩
    rw [← Fl.F.left_inv h1, h2, hF]
    congr 1
    push_cast
    ring
  have hcl : closure A ∩ I ⊆ A := by
    rintro s' ⟨hsc, hs'⟩
    refine ⟨hs', ?_⟩
    have hfr : ∃ᶠ s'' in 𝓝 s', s'' ∈ A := mem_closure_iff_frequently.1 hsc
    have ht := (hc1.tendsto s').prodMk_nhds (hc2 s' hs').tendsto
    exact isClosed_diagonal.mem_of_frequently_of_tendsto (hfr.mono fun _ h ↦ h.2) ht
  have h0 : (0 : ℝ) ∈ A := ⟨⟨by linarith, hR0⟩, by simpa using h₀⟩
  exact ((convex_Ioo (-R) R).isPreconnected.subset_of_closure_inter_subset hAo ⟨0, h0.1, h0⟩
    hcl (show s ∈ I from abs_lt.1 hs)).2

/-- A vertical curve does not return to a point at small times. -/
theorem exists_ne [T2Space C] (t : ℝ) : ∃ ρ > 0, ∀ s, 0 < |s| → |s| < ρ → τ (t + s) ≠ τ t := by
  obtain ⟨Fl, ht, -⟩ := hτ t
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 Fl.F.open_target _ (Fl.F.map_source ht)
  refine ⟨ρ, hρ, fun s hs0 hs h ↦ ?_⟩
  have h₀ : τ t = Fl.F.symm (Fl.F (τ t)) := (Fl.F.left_inv ht).symm
  have hl := hτ.line Fl hball h₀ hs
  have this : Fl.F.symm (Fl.F (τ t)) = Fl.F.symm (Fl.F (τ t) - Complex.I * (s : ℂ)) :=
    (Fl.F.left_inv ht).trans (h.symm.trans hl)
  have hmem : Fl.F (τ t) - Complex.I * (s : ℂ) ∈ Fl.F.target := by
    refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I,
      one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact hs
  have := Fl.F.symm.injOn (Fl.F.map_source ht) hmem this
  have hs' : Complex.I * (s : ℂ) = 0 := by linear_combination this
  simp only [mul_eq_zero, Complex.I_ne_zero, Complex.ofReal_eq_zero, false_or] at hs'
  rw [hs', abs_zero] at hs0
  exact lt_irrefl _ hs0

/-- **A returning vertical curve has a least period, on which it is injective.** -/
theorem exists_minPeriod [T2Space C] {t₁ t₂ : ℝ} (h12 : t₁ ≠ t₂) (h : τ t₁ = τ t₂) :
    ∃ T > 0, Function.Periodic τ T ∧ ∀ s₁ ∈ Ico (0 : ℝ) T, ∀ s₂ ∈ Ico (0 : ℝ) T,
      τ s₁ = τ s₂ → s₁ = s₂ := by
  have hper : ∀ {a b : ℝ}, τ a = τ b → Function.Periodic τ (b - a) := by
    intro a b hab x
    have := hτ.shift_eq hτ hab (x - a)
    rw [show a + (x - a) = x by ring, show b + (x - a) = x + (b - a) by ring] at this
    exact this.symm
  obtain ⟨ρ, hρ, hne⟩ := hτ.exists_ne 0
  set S := {T : ℝ | ρ ≤ T ∧ τ T = τ 0}
  have hSmem : ∀ T, 0 < T → τ T = τ 0 → T ∈ S := by
    intro T hT hTe
    refine ⟨?_, hTe⟩
    by_contra hlt
    push Not at hlt
    refine hne T (by rw [abs_of_pos hT]; exact hT) (by rw [abs_of_pos hT]; exact hlt) ?_
    simpa using hTe
  have hSne : S.Nonempty := by
    refine ⟨|t₂ - t₁|, hSmem _ (abs_pos.2 (sub_ne_zero.2 h12.symm)) ?_⟩
    rcases le_total t₁ t₂ with hle | hle
    · rw [abs_of_nonneg (sub_nonneg.2 hle)]
      simpa using hper h 0
    · rw [abs_of_nonpos (sub_nonpos.2 hle), neg_sub]
      simpa using hper h.symm 0
  have hSc : IsClosed S := (isClosed_le continuous_const continuous_id).inter
    (isClosed_eq hτ.continuous continuous_const)
  have hSb : BddBelow S := ⟨ρ, fun T hT ↦ hT.1⟩
  set T := sInf S
  have hT : T ∈ S := hSc.csInf_mem hSne hSb
  have hTpos : 0 < T := lt_of_lt_of_le hρ hT.1
  refine ⟨T, hTpos, by simpa using hper hT.2.symm, fun s₁ hs₁ s₂ hs₂ he ↦ ?_⟩
  by_contra hne'
  wlog hlt : s₁ < s₂ generalizing s₁ s₂
  · exact this s₂ hs₂ s₁ hs₁ he.symm (Ne.symm hne') (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne'))
  have := hτ.shift_eq hτ he (-s₁)
  rw [add_neg_cancel] at this
  have hmem := hSmem (s₂ + -s₁) (by linarith) this.symm
  have := csInf_le hSb hmem
  linarith [hs₂.2, hs₁.1]

end b3Unimod_Vertical

/-! ## Existence of vertical curves -/

theorem b3Unimod_norm_I_mul (s : ℝ) : ‖Complex.I * (s : ℂ)‖ = |s| := by
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

theorem b3Unimod_floor_iff {a : ℝ} (ha : 0 < a) (k : ℤ) (s : ℝ) :
    ⌊s / a⌋ = k ↔ k * a ≤ s ∧ s < (k + 1) * a := by
  rw [Int.floor_eq_iff, le_div_iff₀ ha, div_lt_iff₀ ha]

/-- **Vertical curves through an invariant set with flat charts of uniform radius.** -/
theorem b3Unimod_exists_vertical [T2Space C] {K : Set C} {ρ : ℝ} (hρ : 0 < ρ)
    (hch : ∀ y ∈ K, ∃ Fl : b3Unimod_Flat hE θ, y ∈ Fl.F.source ∧
      Metric.ball (Fl.F y) ρ ⊆ Fl.F.target)
    (hK : ∀ y ∈ K, ∀ Fl : b3Unimod_Flat hE θ, y ∈ Fl.F.source →
      Metric.ball (Fl.F y) ρ ⊆ Fl.F.target →
        ∀ s : ℝ, |s| < ρ → Fl.F.symm (Fl.F y - Complex.I * (s : ℂ)) ∈ K)
    {p : C} (hp : p ∈ K) :
    ∃ τ : ℝ → C, b3Unimod_Vertical hE θ τ ∧ τ 0 = p ∧ ∀ t, τ t ∈ K := by
  choose ch hch1 hch2 using fun y : K ↦ hch y.1 y.2
  set a := ρ / 3 with ha_def
  have ha : 0 < a := by positivity
  have hball : ∀ (y : K) (s : ℝ), |s| < ρ →
      (ch y).F y - Complex.I * (s : ℂ) ∈ (ch y).F.target := fun y s hs ↦ hch2 y (by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, b3Unimod_norm_I_mul]
    exact hs)
  have hstep : ∀ (y : K) (s : ℝ), |s| < ρ →
      (ch y).F.symm ((ch y).F y - Complex.I * (s : ℂ)) ∈ K :=
    fun y s hs ↦ hK y.1 y.2 (ch y) (hch1 y) (hch2 y) s hs
  have haρ : |a| < ρ := by rw [abs_of_pos ha]; linarith
  have haρ' : |-a| < ρ := by rw [abs_neg]; exact haρ
  let next : K → K := fun y ↦ ⟨_, hstep y a haρ⟩
  let prev : K → K := fun y ↦ ⟨_, hstep y (-a) haρ'⟩
  let Yf : ℕ → K := fun n ↦ next^[n] ⟨p, hp⟩
  let Yb : ℕ → K := fun n ↦ prev^[n] ⟨p, hp⟩
  let Y : ℤ → K := fun k ↦ match k with
    | Int.ofNat n => Yf n
    | Int.negSucc n => Yb (n + 1)
  -- the backward step is undone by the forward step
  have hback : ∀ y : K, ((ch (prev y)).F.symm ((ch (prev y)).F (prev y) -
      Complex.I * (a : ℂ)) : C) = y := by
    intro y
    set z := prev y
    have hz : (z : C) = (ch y).F.symm ((ch y).F y - Complex.I * ((-a : ℝ) : ℂ)) := rfl
    have hR : Metric.ball ((ch z).F z) (2 * a) ⊆ (ch z).F.target :=
      (Metric.ball_subset_ball (by linarith)).trans (hch2 z)
    have hR' : Metric.ball ((ch y).F y - Complex.I * ((-a : ℝ) : ℂ)) (2 * a) ⊆
        (ch y).F.target := by
      refine (Metric.ball_subset_ball' ?_).trans (hch2 y)
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, b3Unimod_norm_I_mul, abs_neg,
        abs_of_pos ha]
      linarith
    have h := (ch z).symm_eq_symm (ch y) hR hR' (by rw [(ch z).F.left_inv (hch1 z), hz])
      (-(Complex.I * (a : ℂ))) (by
        rw [mem_ball_zero_iff, norm_neg, b3Unimod_norm_I_mul, abs_of_pos ha]; linarith)
    rw [← sub_eq_add_neg] at h
    rw [h]
    have : (ch y).F y - Complex.I * ((-a : ℝ) : ℂ) + -(Complex.I * (a : ℂ)) = (ch y).F y := by
      push_cast; ring
    rw [this, (ch y).F.left_inv (hch1 y)]
  have hYnat : ∀ n : ℕ, Y (n : ℤ) = Yf n := fun n ↦ rfl
  have hYneg : ∀ n : ℕ, Y (Int.negSucc n + 1) = Yb n := by
    intro n
    cases n with
    | zero => rfl
    | succ m =>
      show Y (Int.negSucc (m + 1) + 1) = Yb (m + 1)
      rw [show Int.negSucc (m + 1) + 1 = Int.negSucc m by rfl]
  have hJ : ∀ k : ℤ, ((ch (Y k)).F.symm ((ch (Y k)).F (Y k) - Complex.I * (a : ℂ)) : C) =
      Y (k + 1) := by
    intro k
    cases k with
    | ofNat n =>
      have e : Y (Int.ofNat n + 1) = next (Yf n) :=
        Function.iterate_succ_apply' next n ⟨p, hp⟩
      rw [e]
    | negSucc n =>
      rw [hYneg n]
      have e : Y (Int.negSucc n) = prev (Yb n) :=
        Function.iterate_succ_apply' prev n ⟨p, hp⟩
      rw [e]
      exact hback (Yb n)
  -- the pieces
  let P : ℤ → ℝ → C := fun k s ↦
    (ch (Y k)).F.symm ((ch (Y k)).F (Y k) - Complex.I * ((s - k * a : ℝ) : ℂ))
  have hP : ∀ k : ℤ, ∀ s, |s - (k + 1) * a| < 2 * a → P k s = P (k + 1) s := by
    intro k s hs
    have hR : Metric.ball ((ch (Y k)).F (Y k) - Complex.I * (a : ℂ)) (2 * a) ⊆
        (ch (Y k)).F.target := by
      refine (Metric.ball_subset_ball' ?_).trans (hch2 (Y k))
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, b3Unimod_norm_I_mul, abs_of_pos ha]
      linarith
    have hR' : Metric.ball ((ch (Y (k + 1))).F (Y (k + 1))) (2 * a) ⊆ (ch (Y (k + 1))).F.target :=
      (Metric.ball_subset_ball (by linarith)).trans (hch2 (Y (k + 1)))
    have h := (ch (Y k)).symm_eq_symm (ch (Y (k + 1))) hR hR'
      (by rw [hJ k, (ch (Y (k + 1))).F.left_inv (hch1 _)])
      (-(Complex.I * ((s - (k + 1) * a : ℝ) : ℂ))) (by
        rw [mem_ball_zero_iff, norm_neg, b3Unimod_norm_I_mul]; exact hs)
    simp only [P]
    convert h using 2
    · push_cast; ring
    · push_cast; ring
  let τ : ℝ → C := fun t ↦ P ⌊t / a⌋ t
  have hτP : ∀ k : ℤ, ∀ s ∈ Ioo (k * a - a) ((k + 1) * a), τ s = P k s := by
    intro k s hs
    by_cases h : k * a ≤ s
    · show P ⌊s / a⌋ s = P k s
      rw [(b3Unimod_floor_iff ha k s).2 ⟨h, hs.2⟩]
    · push Not at h
      have hfl : ⌊s / a⌋ = k - 1 := (b3Unimod_floor_iff ha (k - 1) s).2
        ⟨by push_cast; linarith [hs.1], by push_cast; linarith⟩
      show P ⌊s / a⌋ s = P k s
      rw [hfl]
      have := hP (k - 1) s (by
        rw [show ((k - 1 : ℤ) : ℝ) + 1 = k by push_cast; ring, abs_lt]
        constructor <;> linarith [hs.1])
      rw [this, sub_add_cancel]
  have hmemP : ∀ k : ℤ, ∀ s, |s - k * a| < ρ →
      (ch (Y k)).F (Y k) - Complex.I * ((s - k * a : ℝ) : ℂ) ∈ (ch (Y k)).F.target :=
    fun k s hs ↦ hball (Y k) _ hs
  have hfl : ∀ t, (⌊t / a⌋ : ℝ) * a ≤ t ∧ t < (⌊t / a⌋ + 1) * a := fun t ↦
    (b3Unimod_floor_iff ha _ t).1 rfl
  refine ⟨τ, fun t ↦ ?_, ?_, fun t ↦ ?_⟩
  · set k := ⌊t / a⌋
    obtain ⟨h1, h2⟩ := hfl t
    have htI : t ∈ Ioo (k * a - a) ((k + 1) * a) := ⟨by linarith, h2⟩
    have hsmall : ∀ s ∈ Ioo (k * a - a) ((k + 1) * a), |s - k * a| < ρ := by
      intro s hs
      rw [abs_lt]
      constructor <;> linarith [hs.1, hs.2]
    refine ⟨ch (Y k), ?_, ?_⟩
    · rw [hτP k t htI]
      exact (ch (Y k)).F.map_target (hmemP k t (hsmall t htI))
    · filter_upwards [isOpen_Ioo.mem_nhds htI] with s hs
      rw [hτP k s hs, hτP k t htI]
      refine ⟨(ch (Y k)).F.map_target (hmemP k s (hsmall s hs)), ?_⟩
      rw [(ch (Y k)).F.right_inv (hmemP k s (hsmall s hs)),
        (ch (Y k)).F.right_inv (hmemP k t (hsmall t htI))]
      push_cast
      ring
  · show P ⌊(0 : ℝ) / a⌋ 0 = p
    simp only [zero_div, Int.floor_zero, P, Int.cast_zero, zero_mul, sub_zero,
      Complex.ofReal_zero, mul_zero]
    exact (ch (Y 0)).F.left_inv (hch1 _)
  · set k := ⌊t / a⌋
    obtain ⟨h1, h2⟩ := hfl t
    exact hstep (Y k) (t - k * a) (by rw [abs_lt]; constructor <;> linarith)

end HodgeLean.Foundations.Program
