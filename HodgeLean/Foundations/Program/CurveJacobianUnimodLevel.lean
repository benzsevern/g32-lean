import HodgeLean.Foundations.Program.CurveJacobianUnimodTraj
import HodgeLean.Foundations.Program.CurveJacobianUnimodDegree

/-! # Track B3, lane Unimod: the level set of the real primitive is a union of vertical loops

Let `θ` have integral real periods, `f` its real primitive mod `1`, and `L = {f ∈ c + ℤ}` a level
set avoiding the zeros of `θ`. Then
* `L` is compact, and has flat charts of a uniform radius `ρ ≤ 1/4` (`b3Unimod_uniform_charts`);
* in a flat chart `F` of radius `ρ` at `y ∈ L`, the points of `L` are those on the vertical line
  `Re F = Re F y` (`b3Unimod_level_re`), and `L` is invariant under the vertical lines;
* every point of `L` lies on a vertical curve in `L` that returns to a point, so it is periodic,
  with a least period on which it is injective (`b3Unimod_exists_closed`);
* the range of such a curve is open in `L` (`b3Unimod_orbit_nhds`).
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

theorem b3Unimod_exists_pos_le {ι : Type*} (t : Finset ι) (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    ∃ ρ > 0, ∀ i ∈ t, ρ ≤ r i := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a t _ ih =>
    obtain ⟨ρ, hρ, h⟩ := ih
    refine ⟨min ρ (r a), lt_min hρ (hr a), fun i hi ↦ ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h i hi)

/-- **Flat charts of a uniform radius** at the points of a compact set without zeros of `θ`. -/
theorem b3Unimod_uniform_charts (hE : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) {K : Set C}
    (hKc : IsCompact K) (hKZ : ∀ y ∈ K, y ∉ b3Unimod_Z θ) :
    ∃ ρ > 0, ∀ y ∈ K, ∃ Fl : b3Unimod_Flat hE θ, y ∈ Fl.F.source ∧
      Metric.ball (Fl.F y) ρ ⊆ Fl.F.target := by
  have hloc : ∀ y : K, ∃ Fl : b3Unimod_Flat hE θ, ∃ r > 0, y.1 ∈ Fl.F.source ∧
      Metric.ball (Fl.F y) (2 * r) ⊆ Fl.F.target := by
    intro y
    obtain ⟨Fl, hy⟩ := b3Unimod_exists_flat hE θ (hKZ y.1 y.2)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 Fl.F.open_target _ (Fl.F.map_source hy)
    exact ⟨Fl, r / 2, by positivity, hy, by rwa [mul_div_cancel₀ _ two_ne_zero]⟩
  choose Fl r hr hy hball using hloc
  have hN : ∀ (y : C) (hy' : y ∈ K), (Fl ⟨y, hy'⟩).F.source ∩
      (Fl ⟨y, hy'⟩).F ⁻¹' Metric.ball ((Fl ⟨y, hy'⟩).F y) (r ⟨y, hy'⟩) ∈ 𝓝 y := by
    intro y hy'
    exact inter_mem ((Fl ⟨y, hy'⟩).F.open_source.mem_nhds (hy ⟨y, hy'⟩))
      (((Fl ⟨y, hy'⟩).F.continuousAt (hy ⟨y, hy'⟩)).preimage_mem_nhds
        (Metric.ball_mem_nhds _ (hr _)))
  obtain ⟨t, ht⟩ := hKc.elim_nhds_subcover' _ hN
  obtain ⟨ρ, hρ, hρr⟩ := b3Unimod_exists_pos_le t r hr
  refine ⟨ρ, hρ, fun y hyK ↦ ?_⟩
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (ht hyK)
  refine ⟨Fl x, hyx.1, fun w hw ↦ hball x ?_⟩
  have h1 : dist w ((Fl x).F y) < ρ := hw
  have h2 : dist ((Fl x).F y) ((Fl x).F x) < r x := hyx.2
  have h3 := hρr x hxt
  rw [Metric.mem_ball]
  calc dist w ((Fl x).F x) ≤ dist w ((Fl x).F y) + dist ((Fl x).F y) ((Fl x).F x) :=
        dist_triangle _ _ _
    _ < 2 * r x := by linarith

theorem b3Unimod_eq_vertical {w a : ℂ} (h : (w - a).re = 0) :
    w = a - Complex.I * ((-(w - a).im : ℝ) : ℂ) := by
  rw [Complex.sub_re] at h
  apply Complex.ext
  · simp; linarith
  · simp

section Level

variable [T2Space C] [ConnectedSpace C] {hE : Module.finrank ℂ E = 1} {θ : b3_HolForm E C}
  (hint : ∀ γ : b3_SmoothLoop E C, ∃ m : ℤ, (b3_period E C γ θ).re = m) (p₀ : C) (c : ℝ)

/-- The level set `{f ∈ c + ℤ}`. -/
def b3Unimod_L (θ : b3_HolForm E C) (p₀ : C) (c : ℝ) : Set C :=
  {y | ∃ m : ℤ, b3Unimod_f θ p₀ y = c + m}

include hint

theorem b3Unimod_segment_sub {Fl : b3Unimod_Flat hE θ} {y : C} {ρ : ℝ}
    (hb : Metric.ball (Fl.F y) ρ ⊆ Fl.F.target) {w : ℂ} (hw : w ∈ Metric.ball (Fl.F y) ρ) :
    segment ℝ (Fl.F y) w ⊆ Fl.F.target :=
  ((convex_ball _ _).segment_subset (Metric.mem_ball_self (lt_of_le_of_lt dist_nonneg hw)) hw).trans
    hb

/-- **`L` is invariant under the vertical lines of flat charts.** -/
theorem b3Unimod_level_inv {y : C} (hy : y ∈ b3Unimod_L θ p₀ c) (Fl : b3Unimod_Flat hE θ)
    (hyF : y ∈ Fl.F.source) {ρ : ℝ} (hb : Metric.ball (Fl.F y) ρ ⊆ Fl.F.target) {s : ℝ}
    (hs : |s| < ρ) : Fl.F.symm (Fl.F y - Complex.I * (s : ℂ)) ∈ b3Unimod_L θ p₀ c := by
  have hw : Fl.F y - Complex.I * (s : ℂ) ∈ Metric.ball (Fl.F y) ρ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, b3Unimod_norm_I_mul]
    exact hs
  obtain ⟨m, hm⟩ := Fl.f_symm hint p₀ hyF (b3Unimod_segment_sub hint hb hw)
  obtain ⟨m', hm'⟩ := hy
  refine ⟨m + m', ?_⟩
  simp only [sub_sub_cancel_left, Complex.neg_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero,
    neg_zero, zero_add] at hm
  push_cast
  linarith

/-- **In a flat chart of radius `≤ 1/4`, `L` is the vertical line through `y`.** -/
theorem b3Unimod_level_re {y : C} (hy : y ∈ b3Unimod_L θ p₀ c) (Fl : b3Unimod_Flat hE θ)
    (hyF : y ∈ Fl.F.source) {ρ : ℝ} (hρ : ρ ≤ 1 / 4)
    (hb : Metric.ball (Fl.F y) ρ ⊆ Fl.F.target) {w : ℂ} (hw : w ∈ Metric.ball (Fl.F y) ρ)
    (hwL : Fl.F.symm w ∈ b3Unimod_L θ p₀ c) : (w - Fl.F y).re = 0 := by
  obtain ⟨m, hm⟩ := Fl.f_symm hint p₀ hyF (b3Unimod_segment_sub hint hb hw)
  obtain ⟨m', hm'⟩ := hy
  obtain ⟨m'', hm''⟩ := hwL
  have hre : (w - Fl.F y).re = (m'' - m' - m : ℤ) := by push_cast; linarith
  have hsmall : |(w - Fl.F y).re| < 1 := by
    calc |(w - Fl.F y).re| ≤ ‖w - Fl.F y‖ := Complex.abs_re_le_norm _
      _ < ρ := by rw [← dist_eq_norm]; exact hw
      _ < 1 := by linarith
  rw [hre] at hsmall ⊢
  have : |((m'' - m' - m : ℤ) : ℝ)| < 1 := hsmall
  rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff] at this
  rw [this, Int.cast_zero]

/-- **Every point of `L` lies on a periodic vertical curve in `L`.** -/
theorem b3Unimod_exists_closed [CompactSpace C] (hE' : Module.finrank ℂ E = 1) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4)
    (hch : ∀ y ∈ b3Unimod_L θ p₀ c, ∃ Fl : b3Unimod_Flat hE θ, y ∈ Fl.F.source ∧
      Metric.ball (Fl.F y) ρ ⊆ Fl.F.target) {p : C} (hp : p ∈ b3Unimod_L θ p₀ c) :
    ∃ τ : ℝ → C, b3Unimod_Vertical hE θ τ ∧ τ 0 = p ∧ (∀ t, τ t ∈ b3Unimod_L θ p₀ c) ∧
      ∃ T > 0, Function.Periodic τ T ∧ ∀ s₁ ∈ Ico (0 : ℝ) T, ∀ s₂ ∈ Ico (0 : ℝ) T,
        τ s₁ = τ s₂ → s₁ = s₂ := by
  obtain ⟨τ, hτ, hτ0, hτL⟩ := b3Unimod_exists_vertical hρ hch
    (fun y hy Fl hyF hb s hs ↦ b3Unimod_level_inv hint p₀ c hy Fl hyF hb hs) hp
  refine ⟨τ, hτ, hτ0, hτL, ?_⟩
  have hLc : IsCompact (b3Unimod_L θ p₀ c) :=
    (b3Unimod_isClosed_level hint hE' p₀ c).isCompact
  obtain ⟨q, hqL, hq⟩ := hLc.exists_mapClusterPt (f := (atTop : Filter ℕ))
    (u := fun n : ℕ ↦ τ n) (tendsto_principal.2 (Eventually.of_forall fun n ↦ hτL n))
  obtain ⟨Fl, hqF, hb⟩ := hch q hqL
  have hN : Fl.F.source ∩ Fl.F ⁻¹' Metric.ball (Fl.F q) (ρ / 3) ∈ 𝓝 q :=
    inter_mem (Fl.F.open_source.mem_nhds hqF)
      ((Fl.F.continuousAt hqF).preimage_mem_nhds (Metric.ball_mem_nhds _ (by positivity)))
  have hfr : ∃ᶠ n : ℕ in atTop, τ n ∈ Fl.F.source ∩ Fl.F ⁻¹' Metric.ball (Fl.F q) (ρ / 3) :=
    hq.frequently hN
  -- from each visit near `q`, the curve reaches `q` within time `ρ / 3`
  have hvisit : ∀ n : ℕ, τ n ∈ Fl.F.source ∩ Fl.F ⁻¹' Metric.ball (Fl.F q) (ρ / 3) →
      ∃ b : ℝ, |b| < ρ / 3 ∧ τ (n + b) = q := by
    intro n ⟨hyF, hyb⟩
    set y := τ n
    set w := Fl.F y
    have hwb : w ∈ Metric.ball (Fl.F q) ρ := Metric.ball_subset_ball (by linarith) hyb
    have hre := b3Unimod_level_re hint p₀ c hqL Fl hqF hρ4 hb hwb
      (by rw [Fl.F.left_inv hyF]; exact hτL _)
    set b := (w - Fl.F q).im
    have hbs : |b| < ρ / 3 := lt_of_le_of_lt (Complex.abs_im_le_norm _)
      (by rw [← dist_eq_norm]; exact hyb)
    have hR : Metric.ball w (2 * ρ / 3) ⊆ Fl.F.target := by
      refine (Metric.ball_subset_ball' ?_).trans hb
      have : dist w (Fl.F q) < ρ / 3 := hyb
      linarith
    have hl := hτ.line Fl hR (Fl.F.left_inv hyF).symm (s := b)
      (lt_of_lt_of_le hbs (by linarith))
    refine ⟨b, hbs, ?_⟩
    rw [hl]
    have : w - Complex.I * (b : ℂ) = Fl.F q := by
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul,
          Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero]
        simpa [sub_eq_zero] using hre
      · simp [b]
    rw [this, Fl.F.left_inv hqF]
  obtain ⟨n1, -, hn1⟩ := frequently_atTop.1 hfr 0
  obtain ⟨n2, hn12, hn2⟩ := frequently_atTop.1 hfr (n1 + 1)
  obtain ⟨b1, hb1, h1⟩ := hvisit n1 hn1
  obtain ⟨b2, hb2, h2⟩ := hvisit n2 hn2
  have hφ1 : (n1 : ℝ) + 1 ≤ n2 := by exact_mod_cast hn12
  have h12 : (n1 : ℝ) + b1 ≠ (n2 : ℝ) + b2 := by
    intro h
    rw [abs_lt] at hb1 hb2
    linarith
  exact hτ.exists_minPeriod h12 (h1.trans h2.symm)

/-- **Orbits are open in `L`.** -/
theorem b3Unimod_orbit_nhds {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4)
    (hch : ∀ y ∈ b3Unimod_L θ p₀ c, ∃ Fl : b3Unimod_Flat hE θ, y ∈ Fl.F.source ∧
      Metric.ball (Fl.F y) ρ ⊆ Fl.F.target) {τ : ℝ → C} (hτ : b3Unimod_Vertical hE θ τ)
    (hτL : ∀ t, τ t ∈ b3Unimod_L θ p₀ c) (t : ℝ) :
    ∃ N ∈ 𝓝 (τ t), N ∩ b3Unimod_L θ p₀ c ⊆ range τ := by
  obtain ⟨Fl, htF, hb⟩ := hch (τ t) (hτL t)
  refine ⟨Fl.F.source ∩ Fl.F ⁻¹' Metric.ball (Fl.F (τ t)) ρ, inter_mem
    (Fl.F.open_source.mem_nhds htF)
    ((Fl.F.continuousAt htF).preimage_mem_nhds (Metric.ball_mem_nhds _ hρ)), ?_⟩
  rintro z ⟨⟨hzF, hzb⟩, hzL⟩
  have hre := b3Unimod_level_re hint p₀ c (hτL t) Fl htF hρ4 hb hzb
    (by rw [Fl.F.left_inv hzF]; exact hzL)
  have hs : |(-(Fl.F z - Fl.F (τ t)).im)| < ρ := by
    rw [abs_neg]
    exact lt_of_le_of_lt (Complex.abs_im_le_norm _) (by rw [← dist_eq_norm]; exact hzb)
  have hl := hτ.line Fl hb (Fl.F.left_inv htF).symm hs
  refine ⟨t + -(Fl.F z - Fl.F (τ t)).im, ?_⟩
  rw [hl, ← b3Unimod_eq_vertical hre, Fl.F.left_inv hzF]

end Level

end HodgeLean.Foundations.Program
