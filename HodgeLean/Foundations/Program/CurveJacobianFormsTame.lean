import HodgeLean.Foundations.Program.CurveJacobianFormsPath

/-!
# Track B3 foundations: tame paths, concatenation and closed loops

A **tame path** (`b3Forms_IsTame`) is a `C¹` map `γ : ℝ → M` that is constant near `(-∞, 0]` and
near `[1, ∞)`. Tame paths can be reversed (`b3Forms_rev`) and concatenated (`b3Forms_concat`) inside
the class, a closed tame path extends periodically to a `C¹` loop (`b3Forms_loopOf`), and line
integrals over `[0, 1]` are additive and change sign accordingly.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Function
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

section Velocity

theorem b3Forms_velocity_congr {γ δ : ℝ → M} {t : ℝ} (h : γ =ᶠ[𝓝 t] δ) :
    b3Forms_velocity (E := E) γ t = b3Forms_velocity δ t := by
  rw [b3Forms_velocity, h.mfderiv_eq]
  rfl

theorem b3Forms_velocity_of_const {γ : ℝ → M} {t : ℝ} {p : M} (h : γ =ᶠ[𝓝 t] fun _ ↦ p) :
    b3Forms_velocity (E := E) γ t = 0 := by
  rw [b3Forms_velocity_congr h, b3Forms_velocity, mfderiv_const]
  rfl

theorem b3Forms_velocity_comp_affine {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ)
    (c d t : ℝ) :
    b3Forms_velocity (E := E) (γ ∘ fun s ↦ c * s + d) t =
      c • b3Forms_velocity γ (c * t + d) := by
  have haff : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (fun s : ℝ ↦ c * s + d) :=
    (contDiff_const.mul contDiff_id |>.add contDiff_const).contMDiff
  have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (γ ∘ fun s ↦ c * s + d) := hγ.comp haff
  rw [b3Forms_velocity_eq (hc.mdifferentiableAt one_ne_zero),
    b3Forms_velocity_eq (hγ.mdifferentiableAt one_ne_zero)]
  have h1 := b3Forms_hasDerivAt_chart_comp hγ (x := γ (c * t + d)) (mem_chart_source E _)
  have h2 : HasDerivAt (fun s : ℝ ↦ c * s + d) c t := by
    simpa using ((hasDerivAt_id t).const_mul c).add_const d
  exact (h1.scomp t h2).deriv

theorem b3Forms_apply_smul_const (A : E [⋀^Fin 1]→L[ℝ] ℝ) (c : ℝ) (v : E) :
    A (fun _ ↦ c • v) = c * A (fun _ ↦ v) := by
  have h := A.map_update_smul (fun _ ↦ v) 0 c v
  have e : ∀ w : E, Function.update (fun _ : Fin 1 ↦ v) 0 w = fun _ ↦ w := fun w ↦ by
    funext i; fin_cases i; simp
  rw [e, e] at h
  rw [h, smul_eq_mul]

theorem b3Forms_apply_zero_const (A : E [⋀^Fin 1]→L[ℝ] ℝ) : A (fun _ ↦ (0 : E)) = 0 := by
  simpa using b3Forms_apply_smul_const A 0 0

end Velocity

section Tame

variable (E) in
/-- **A tame path**: a `C¹` map `ℝ → M`, constant near `(-∞, 0]` and near `[1, ∞)`.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 11 (conservative covector
fields) and Ch. 17 (de Rham's theorem in degree one); Forster, *Lectures on Riemann Surfaces*, GTM
81, §10. -/
def b3Forms_IsTame (γ : ℝ → M) : Prop :=
  ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ ∧
    ∃ ε > 0, (∀ t, t < ε → γ t = γ 0) ∧ (∀ t, 1 - ε < t → γ t = γ 1)

theorem b3Forms_isTame_const (p : M) : b3Forms_IsTame E (fun _ : ℝ ↦ p) :=
  ⟨contMDiff_const, 1, one_pos, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

/-- A path is `C¹` if it is `C¹` near every point. -/
theorem b3Forms_contMDiff_of_locally {γ : ℝ → M}
    (h : ∀ t, ∃ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 δ ∧ γ =ᶠ[𝓝 t] δ) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ := fun t ↦ by
  obtain ⟨δ, hδ, hγδ⟩ := h t
  exact (hδ t).congr_of_eventuallyEq hγδ

theorem b3Forms_contMDiff_comp_affine {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ)
    (c d : ℝ) : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (γ ∘ fun s ↦ c * s + d) :=
  hγ.comp (contDiff_const.mul contDiff_id |>.add contDiff_const).contMDiff

/-- **The reversed path** `t ↦ γ (1 - t)`.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 11 (conservative covector
fields) and Ch. 17 (de Rham's theorem in degree one); Forster, *Lectures on Riemann Surfaces*, GTM
81, §10. -/
def b3Forms_rev (γ : ℝ → M) : ℝ → M := fun t ↦ γ (1 - t)

theorem b3Forms_rev_eq (γ : ℝ → M) : b3Forms_rev γ = γ ∘ fun s ↦ (-1) * s + 1 := by
  funext t
  simp [b3Forms_rev]
  ring_nf

theorem b3Forms_IsTame.rev {γ : ℝ → M} (hγ : b3Forms_IsTame E γ) :
    b3Forms_IsTame E (b3Forms_rev γ) := by
  obtain ⟨hc, ε, hε, h0, h1⟩ := hγ
  refine ⟨by rw [b3Forms_rev_eq]; exact b3Forms_contMDiff_comp_affine hc _ _, ε, hε,
    fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · simp only [b3Forms_rev, sub_zero]
    exact h1 _ (by linarith)
  · simp only [b3Forms_rev, sub_self]
    exact h0 _ (by linarith)

/-- **The line integral over the reversed path** changes sign. -/
theorem b3Forms_lineIntegral_rev (α : M → E [⋀^Fin 1]→L[ℝ] ℝ) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) :
    b3Forms_lineIntegral α (b3Forms_rev γ) 0 1 = -b3Forms_lineIntegral α γ 0 1 := by
  have h : ∀ t, α (b3Forms_rev γ t) (fun _ ↦ b3Forms_velocity (b3Forms_rev γ) t) =
      -(α (γ (1 - t)) (fun _ ↦ b3Forms_velocity γ (1 - t))) := by
    intro t
    rw [b3Forms_rev_eq, b3Forms_velocity_comp_affine hγ, b3Forms_apply_smul_const]
    simp only [Function.comp_apply]
    ring_nf
  rw [b3Forms_lineIntegral, b3Forms_lineIntegral]
  simp_rw [h]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_left
    (fun t ↦ α (γ t) (fun _ ↦ b3Forms_velocity γ t)) 1]
  norm_num

/-- **The concatenation** of two paths, `γ` on `[0, 1/2]` and `δ` on `[1/2, 1]`.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 11 (conservative covector
fields) and Ch. 17 (de Rham's theorem in degree one); Forster, *Lectures on Riemann Surfaces*, GTM
81, §10. -/
def b3Forms_concat (γ δ : ℝ → M) : ℝ → M :=
  fun t ↦ if t ≤ 1 / 2 then γ (2 * t) else δ (2 * t - 1)

theorem b3Forms_concat_eventuallyEq_left (γ δ : ℝ → M) {t : ℝ} (ht : t < 1 / 2) :
    b3Forms_concat γ δ =ᶠ[𝓝 t] γ ∘ fun s ↦ 2 * s + 0 := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  have hs' : s ≤ 1 / 2 := le_of_lt hs
  simp only [b3Forms_concat, ite_eq_left hs', Function.comp_apply, add_zero]

theorem b3Forms_concat_eventuallyEq_right (γ δ : ℝ → M) {t : ℝ} (ht : 1 / 2 < t) :
    b3Forms_concat γ δ =ᶠ[𝓝 t] δ ∘ fun s ↦ 2 * s + (-1) := by
  filter_upwards [Ioi_mem_nhds ht] with s hs
  have hs' : ¬ s ≤ 1 / 2 := not_le.2 hs
  simp only [b3Forms_concat, ite_eq_right hs', Function.comp_apply, sub_eq_add_neg]

theorem b3Forms_IsTame.eventually_left {γ : ℝ → M} (hγ : b3Forms_IsTame E γ) :
    γ =ᶠ[𝓝 0] fun _ ↦ γ 0 := by
  obtain ⟨_, ε, hε, h0, _⟩ := hγ
  filter_upwards [Iio_mem_nhds hε] with s hs
  exact h0 s hs

theorem b3Forms_IsTame.eventually_right {γ : ℝ → M} (hγ : b3Forms_IsTame E γ) :
    γ =ᶠ[𝓝 1] fun _ ↦ γ 1 := by
  obtain ⟨_, ε, hε, _, h1⟩ := hγ
  filter_upwards [Ioi_mem_nhds (show 1 - ε < 1 by linarith)] with s hs
  exact h1 s hs

theorem b3Forms_concat_eventuallyEq_mid {γ δ : ℝ → M} (hγ : b3Forms_IsTame E γ)
    (hδ : b3Forms_IsTame E δ) (h : γ 1 = δ 0) :
    b3Forms_concat γ δ =ᶠ[𝓝 (1 / 2)] fun _ ↦ γ 1 := by
  obtain ⟨_, ε, hε, _, h1⟩ := hγ
  obtain ⟨_, ε', hε', h0', _⟩ := hδ
  have hm : (0 : ℝ) < min ε ε' / 2 := by positivity
  filter_upwards [Metric.ball_mem_nhds (1 / 2 : ℝ) hm] with s hs
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
  have hmin1 := min_le_left ε ε'
  have hmin2 := min_le_right ε ε'
  by_cases hs' : s ≤ 1 / 2
  · simp only [b3Forms_concat, ite_eq_left hs']
    exact h1 _ (by linarith)
  · simp only [b3Forms_concat, ite_eq_right hs']
    rw [h]
    exact h0' _ (by linarith)

theorem b3Forms_IsTame.concat {γ δ : ℝ → M} (hγ : b3Forms_IsTame E γ) (hδ : b3Forms_IsTame E δ)
    (h : γ 1 = δ 0) : b3Forms_IsTame E (b3Forms_concat γ δ) := by
  refine ⟨b3Forms_contMDiff_of_locally fun t ↦ ?_, ?_⟩
  · rcases lt_trichotomy t (1 / 2) with ht | rfl | ht
    · exact ⟨_, b3Forms_contMDiff_comp_affine hγ.1 2 0, b3Forms_concat_eventuallyEq_left γ δ ht⟩
    · exact ⟨_, contMDiff_const, b3Forms_concat_eventuallyEq_mid hγ hδ h⟩
    · exact ⟨_, b3Forms_contMDiff_comp_affine hδ.1 2 (-1),
        b3Forms_concat_eventuallyEq_right γ δ ht⟩
  · obtain ⟨_, ε, hε, h0, _⟩ := hγ
    obtain ⟨_, ε', hε', _, h1'⟩ := hδ
    have hmin1 := min_le_left (min ε ε') 1
    have hmin2 := min_le_right (min ε ε') 1
    have hmin3 := min_le_left ε ε'
    have hmin4 := min_le_right ε ε'
    have hpos : 0 < min (min ε ε') 1 / 2 := by positivity
    refine ⟨min (min ε ε') 1 / 2, hpos, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
    · have ht' : t ≤ 1 / 2 := by linarith
      simp only [b3Forms_concat, ite_eq_left ht', ite_eq_left (show (0 : ℝ) ≤ 1 / 2 by norm_num),
        mul_zero]
      exact h0 _ (by linarith)
    · have ht' : ¬ t ≤ 1 / 2 := by linarith
      simp only [b3Forms_concat, ite_eq_right ht',
        ite_eq_right (show ¬ (1 : ℝ) ≤ 1 / 2 by norm_num)]
      norm_num
      exact h1' _ (by linarith)

/-- The integrand of a line integral.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 11 (line integrals of
covector fields); Mathlib `mfderiv`. -/
def b3Forms_integrand (α : M → E [⋀^Fin 1]→L[ℝ] ℝ) (γ : ℝ → M) (t : ℝ) : ℝ :=
  α (γ t) (fun _ ↦ b3Forms_velocity γ t)

theorem b3Forms_lineIntegral_eq_integrand (α : M → E [⋀^Fin 1]→L[ℝ] ℝ) (γ : ℝ → M) (a b : ℝ) :
    b3Forms_lineIntegral α γ a b = ∫ t in a..b, b3Forms_integrand α γ t := rfl

theorem b3Forms_integrand_comp_affine (α : M → E [⋀^Fin 1]→L[ℝ] ℝ) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (c d t : ℝ) :
    b3Forms_integrand α (γ ∘ fun s ↦ c * s + d) t = c * b3Forms_integrand α γ (c * t + d) := by
  simp only [b3Forms_integrand, b3Forms_velocity_comp_affine hγ, b3Forms_apply_smul_const,
    Function.comp_apply]

theorem b3Forms_integrand_congr (α : M → E [⋀^Fin 1]→L[ℝ] ℝ) {γ δ : ℝ → M} {t : ℝ}
    (h : γ =ᶠ[𝓝 t] δ) : b3Forms_integrand α γ t = b3Forms_integrand α δ t := by
  simp only [b3Forms_integrand, b3Forms_velocity_congr h, h.eq_of_nhds]

theorem b3Forms_integrand_of_const (α : M → E [⋀^Fin 1]→L[ℝ] ℝ) {γ : ℝ → M} {t : ℝ} {p : M}
    (h : γ =ᶠ[𝓝 t] fun _ ↦ p) : b3Forms_integrand α γ t = 0 := by
  simp only [b3Forms_integrand, b3Forms_velocity_of_const h, b3Forms_apply_zero_const]

/-- **The line integral over a concatenation** is the sum of the line integrals. -/
theorem b3Forms_lineIntegral_concat {α : M → E [⋀^Fin 1]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α)
    {γ δ : ℝ → M} (hγ : b3Forms_IsTame E γ) (hδ : b3Forms_IsTame E δ) (h : γ 1 = δ 0) :
    b3Forms_lineIntegral α (b3Forms_concat γ δ) 0 1 =
      b3Forms_lineIntegral α γ 0 1 + b3Forms_lineIntegral α δ 0 1 := by
  have hc := (hγ.concat hδ h).1
  simp only [b3Forms_lineIntegral_eq_integrand]
  have hint : ∀ a b, IntervalIntegrable (b3Forms_integrand α (b3Forms_concat γ δ)) volume a b :=
    fun a b ↦ b3Forms_intervalIntegrable_lineIntegrand hα hc a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2) (hint 0 (1 / 2))
    (hint (1 / 2) 1)]
  have hmid : b3Forms_integrand α (b3Forms_concat γ δ) (1 / 2) = 0 :=
    b3Forms_integrand_of_const α (b3Forms_concat_eventuallyEq_mid hγ hδ h)
  have hγ1 : b3Forms_integrand α γ 1 = 0 := b3Forms_integrand_of_const α hγ.eventually_right
  have hδ0 : b3Forms_integrand α δ 0 = 0 := b3Forms_integrand_of_const α hδ.eventually_left
  have e1 : EqOn (b3Forms_integrand α (b3Forms_concat γ δ))
      (fun t ↦ 2 * b3Forms_integrand α γ (2 * t)) (uIcc 0 (1 / 2)) := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    rcases ht.2.lt_or_eq with ht' | rfl
    · rw [b3Forms_integrand_congr α (b3Forms_concat_eventuallyEq_left γ δ ht'),
        b3Forms_integrand_comp_affine α hγ.1, add_zero]
    · simp only [hmid, show (2 : ℝ) * (1 / 2) = 1 by norm_num, hγ1, mul_zero]
  have e2 : EqOn (b3Forms_integrand α (b3Forms_concat γ δ))
      (fun t ↦ 2 * b3Forms_integrand α δ (2 * t - 1)) (uIcc (1 / 2) 1) := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    rcases ht.1.lt_or_eq with ht' | rfl
    · rw [b3Forms_integrand_congr α (b3Forms_concat_eventuallyEq_right γ δ ht'),
        b3Forms_integrand_comp_affine α hδ.1, ← sub_eq_add_neg]
    · simp only [hmid, show (2 : ℝ) * (1 / 2) - 1 = 0 by norm_num, hδ0, mul_zero]
  rw [intervalIntegral.integral_congr e1, intervalIntegral.integral_congr e2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left _ two_ne_zero,
    intervalIntegral.integral_comp_mul_sub _ two_ne_zero]
  norm_num
  ring

/-- **The loop of a closed path**: the periodic extension `t ↦ γ (fract t)`.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 11 (conservative covector
fields) and Ch. 17 (de Rham's theorem in degree one); Forster, *Lectures on Riemann Surfaces*, GTM
81, §10. -/
def b3Forms_loopOf (γ : ℝ → M) : ℝ → M := fun t ↦ γ (Int.fract t)

theorem b3Forms_loopOf_periodic (γ : ℝ → M) : Function.Periodic (b3Forms_loopOf γ) 1 :=
  fun t ↦ by simp [b3Forms_loopOf]

theorem b3Forms_loopOf_eventuallyEq_int {γ : ℝ → M} (hγ : b3Forms_IsTame E γ) (h : γ 0 = γ 1)
    (n : ℤ) : b3Forms_loopOf γ =ᶠ[𝓝 (n : ℝ)] fun _ ↦ γ 0 := by
  obtain ⟨_, ε, hε, h0, h1⟩ := hγ
  have hm : (0 : ℝ) < min ε 1 := lt_min hε one_pos
  filter_upwards [Metric.ball_mem_nhds (n : ℝ) hm] with s hs
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
  have hm1 := min_le_left ε 1
  have hm2 := min_le_right ε 1
  simp only [b3Forms_loopOf]
  by_cases hsn : (n : ℝ) ≤ s
  · have hfl : ⌊s⌋ = n := Int.floor_eq_iff.2 ⟨hsn, by linarith⟩
    rw [Int.fract, hfl]
    exact h0 _ (by linarith)
  · have hfl : ⌊s⌋ = n - 1 := Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
    rw [Int.fract, hfl, h]
    push_cast
    exact h1 _ (by linarith)

theorem b3Forms_loopOf_eventuallyEq_of_mem {γ : ℝ → M} {t : ℝ} {n : ℤ}
    (ht : t ∈ Ioo (n : ℝ) (n + 1)) :
    b3Forms_loopOf γ =ᶠ[𝓝 t] γ ∘ fun s ↦ 1 * s + (-(n : ℝ)) := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  have hfl : ⌊s⌋ = n := Int.floor_eq_iff.2 ⟨hs.1.le, hs.2⟩
  simp [b3Forms_loopOf, Int.fract, hfl, sub_eq_add_neg]

/-- The loop of a closed tame path is `C¹`. -/
theorem b3Forms_IsTame.contMDiff_loopOf {γ : ℝ → M} (hγ : b3Forms_IsTame E γ) (h : γ 0 = γ 1) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (b3Forms_loopOf γ) := by
  refine b3Forms_contMDiff_of_locally fun t ↦ ?_
  by_cases ht : Int.fract t = 0
  · obtain ⟨n, hn⟩ := Int.fract_eq_zero_iff.1 ht
    rw [← hn]
    exact ⟨_, contMDiff_const, b3Forms_loopOf_eventuallyEq_int hγ h n⟩
  · refine ⟨_, b3Forms_contMDiff_comp_affine hγ.1 1 (-(⌊t⌋ : ℝ)),
      b3Forms_loopOf_eventuallyEq_of_mem ⟨?_, Int.lt_floor_add_one t⟩⟩
    exact lt_of_le_of_ne (Int.floor_le t) fun h' ↦ ht (by rw [← h']; simp)

/-- **The period of the loop of a closed tame path** is the line integral over the path. -/
theorem b3Forms_lineIntegral_loopOf (α : M → E [⋀^Fin 1]→L[ℝ] ℝ) {γ : ℝ → M}
    (hγ : b3Forms_IsTame E γ) (h : γ 0 = γ 1) :
    b3Forms_lineIntegral α (b3Forms_loopOf γ) 0 1 = b3Forms_lineIntegral α γ 0 1 := by
  simp only [b3Forms_lineIntegral_eq_integrand]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le zero_le_one] at ht
  rcases ht.1.lt_or_eq with ht0 | rfl
  · rcases ht.2.lt_or_eq with ht1 | rfl
    · rw [b3Forms_integrand_congr α (b3Forms_loopOf_eventuallyEq_of_mem (n := 0)
        ⟨by simpa using ht0, by simpa using ht1⟩), b3Forms_integrand_comp_affine α hγ.1]
      simp
    · rw [b3Forms_integrand_of_const α (by simpa using b3Forms_loopOf_eventuallyEq_int hγ h 1),
        b3Forms_integrand_of_const α hγ.eventually_right]
  · rw [b3Forms_integrand_of_const α (by simpa using b3Forms_loopOf_eventuallyEq_int hγ h 0),
      b3Forms_integrand_of_const α hγ.eventually_left]

end Tame

end HodgeLean.Foundations.Program
