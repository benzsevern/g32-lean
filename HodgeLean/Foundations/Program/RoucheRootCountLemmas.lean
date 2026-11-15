import HodgeLean.Foundations.Program.RoucheRootCountDefs

/-! # Rouché and Pellet root counts for complex polynomials

Mathlib-only proofs. The circle integral of `p' / p` equals `2πi` times the number of roots in
the open disc, by the root expansion of the logarithmic derivative; boundary dominance puts
`p / q` in the right half-plane, where `log (p / q)` is a primitive of `p' / p − q' / q`.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.Program

open Polynomial Complex Metric
open scoped Real

open Classical in
/-- The circle integral of `(z − α)⁻¹`, for `α` off the circle, is `2πi` or `0`. -/
theorem rou_circleIntegral_sub_inv (c α : ℂ) {r : ℝ} (hr : 0 < r) (hα : α ∉ sphere c r) :
    (∮ z in C(c, r), (z - α)⁻¹) = if α ∈ ball c r then 2 * π * I else 0 := by
  split_ifs with hb
  · exact circleIntegral.integral_sub_inv_of_mem_ball hb
  · have hout : r < dist α c := by
      rw [mem_ball, not_lt] at hb
      rw [mem_sphere] at hα
      exact lt_of_le_of_ne hb (Ne.symm hα)
    have hne : ∀ z ∈ closedBall c r, z - α ≠ 0 := fun z hz h => by
      rw [sub_eq_zero] at h
      subst h
      exact absurd (mem_closedBall.1 hz) (not_le.2 hout)
    refine DiffContOnCl.circleIntegral_eq_zero hr.le ⟨?_, ?_⟩
    · intro z hz
      exact ((differentiableAt_id.sub_const α).inv
        (hne z (ball_subset_closedBall hz))).differentiableWithinAt
    · rw [closure_ball c hr.ne']
      exact (continuousOn_id.sub continuousOn_const).inv₀ hne

open Classical in
/-- Circle integral of a finite sum of `(z − α)⁻¹` over a multiset of points off the circle. -/
theorem rou_circleIntegral_multiset_sum (c : ℂ) {r : ℝ} (hr : 0 < r) (s : Multiset ℂ)
    (hs : ∀ α ∈ s, α ∉ sphere c r) :
    (∮ z in C(c, r), (s.map fun α => (z - α)⁻¹).sum) =
      2 * π * I * (Multiset.card (s.filter (· ∈ ball c r)) : ℂ) := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp [circleIntegral]
  | cons a s ih =>
    have ha : a ∉ sphere c r := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ α ∈ s, α ∉ sphere c r := fun α h => hs α (Multiset.mem_cons_of_mem h)
    have hcont : ∀ β ∉ sphere c r, ContinuousOn (fun z : ℂ => (z - β)⁻¹) (sphere c r) :=
      fun β hβ => (continuousOn_id.sub continuousOn_const).inv₀ fun z hz h => by
        have : z = β := by simpa [sub_eq_zero] using h
        subst this; exact hβ hz
    have hint : CircleIntegrable (fun z => (s.map fun α => (z - α)⁻¹).sum) c r := by
      refine ContinuousOn.circleIntegrable hr.le ?_
      have : (fun z => (s.map fun α => (z - α)⁻¹).sum) =
          fun z => ∑ α ∈ s.toFinset, (s.count α : ℂ) * (z - α)⁻¹ := by
        funext z
        rw [Finset.sum_multiset_map_count]
        simp [nsmul_eq_mul]
      rw [this]
      exact continuousOn_finsetSum _ fun β hβ =>
        continuousOn_const.mul (hcont β (hs' β (Multiset.mem_toFinset.1 hβ)))
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [circleIntegral.integral_add ((hcont a ha).circleIntegrable hr.le) hint, ih hs',
      rou_circleIntegral_sub_inv c a hr ha, Multiset.filter_cons]
    split_ifs with hb <;> simp [mul_add, add_comm]

/-- The argument principle for a polynomial without zeros on the circle. -/
theorem rou_circleIntegral_logDeriv (p : ℂ[X]) (c : ℂ) {r : ℝ} (hr : 0 < r)
    (hp : ∀ z ∈ sphere c r, p.eval z ≠ 0) :
    (∮ z in C(c, r), p.derivative.eval z / p.eval z) =
      2 * π * I * (rou_discCount p c r : ℂ) := by
  classical
  have hroot : ∀ α ∈ p.roots, α ∉ sphere c r := fun α hα hs =>
    hp α hs (isRoot_of_mem_roots hα)
  have hcongr : Set.EqOn (fun z => p.derivative.eval z / p.eval z)
      (fun z => (p.roots.map fun α => (z - α)⁻¹).sum) (sphere c r) := by
    intro z hz
    simp only [(IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero (hp z hz), one_div]
  rw [circleIntegral.integral_congr hr.le hcongr, rou_circleIntegral_multiset_sum c hr _ hroot,
    rou_discCount]

theorem rou_discCount_of_nonpos (p : ℂ[X]) (c : ℂ) {r : ℝ} (hr : r ≤ 0) :
    rou_discCount p c r = 0 := by
  classical
  rw [rou_discCount, Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro a _ ha
  rw [ball_eq_empty.2 hr] at ha
  exact ha

theorem rou_rouche_poly (p q : ℂ[X]) (c : ℂ) (r : ℝ)
    (h : ∀ z ∈ Metric.sphere c r, ‖(p - q).eval z‖ < ‖q.eval z‖) :
    rou_discCount p c r = rou_discCount q c r := by
  rcases le_or_gt r 0 with hr | hr
  · rw [rou_discCount_of_nonpos p c hr, rou_discCount_of_nonpos q c hr]
  have hq : ∀ z ∈ sphere c r, q.eval z ≠ 0 := fun z hz h0 => by
    have := h z hz
    rw [h0, norm_zero] at this
    exact (norm_nonneg _).not_gt this
  have hp : ∀ z ∈ sphere c r, p.eval z ≠ 0 := fun z hz h0 => by
    have := h z hz
    rw [eval_sub, h0, zero_sub, norm_neg] at this
    exact lt_irrefl _ this
  have hslit : ∀ z ∈ sphere c r, p.eval z / q.eval z ∈ slitPlane := by
    intro z hz
    refine mem_slitPlane_iff.2 (Or.inl ?_)
    have hqz := hq z hz
    have hlt : ‖(p - q).eval z / q.eval z‖ < 1 := by
      rw [norm_div, div_lt_one (norm_pos_iff.2 hqz)]
      exact h z hz
    have hre : p.eval z / q.eval z = 1 + (p - q).eval z / q.eval z := by
      rw [eval_sub]; field_simp; ring
    rw [hre, add_re, one_re]
    have := (abs_re_le_norm ((p - q).eval z / q.eval z))
    linarith [neg_abs_le ((p - q).eval z / q.eval z).re]
  have hder : ∀ z ∈ sphere c r, HasDerivWithinAt (fun w => log (p.eval w / q.eval w))
      (p.derivative.eval z / p.eval z - q.derivative.eval z / q.eval z) (sphere c r) z := by
    intro z hz
    refine HasDerivAt.hasDerivWithinAt ?_
    convert ((p.hasDerivAt z).div (q.hasDerivAt z) (hq z hz)).clog (hslit z hz) using 1
    rw [Pi.div_apply]
    field_simp [hp z hz, hq z hz]
  have hzero := circleIntegral.integral_eq_zero_of_hasDerivWithinAt hr.le hder
  have hcont : ∀ f : ℂ[X], (∀ z ∈ sphere c r, f.eval z ≠ 0) →
      CircleIntegrable (fun z => f.derivative.eval z / f.eval z) c r := fun f hf =>
    ContinuousOn.circleIntegrable hr.le
      (f.derivative.continuousOn.div f.continuousOn hf)
  rw [circleIntegral.integral_sub (hcont p hp) (hcont q hq), rou_circleIntegral_logDeriv p c hr hp,
    rou_circleIntegral_logDeriv q c hr hq, sub_eq_zero] at hzero
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  exact_mod_cast mul_left_cancel₀ h2 hzero

/-- Expansion of `p` in powers of `z − c`, through its Taylor coefficients at `c`. -/
theorem rou_eval_eq_sum_taylor (p : ℂ[X]) (c z : ℂ) :
    p.eval z = ∑ k ∈ Finset.range ((taylor c p).natDegree + 1),
      (taylor c p).coeff k * (z - c) ^ k := by
  rw [← eval_eq_sum_range, taylor_eval, sub_add_cancel]

theorem rou_pelletTail_nonneg (p : ℂ[X]) (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (m : ℕ) :
    0 ≤ rou_pelletTail p c r m :=
  Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (pow_nonneg hr k)

theorem rou_norm_sum_erase_le (p : ℂ[X]) (c z : ℂ) {r : ℝ} (m : ℕ) (hz : ‖z - c‖ ≤ r) :
    ‖∑ k ∈ (Finset.range ((taylor c p).natDegree + 1)).erase m,
        (taylor c p).coeff k * (z - c) ^ k‖ ≤ rou_pelletTail p c r m :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => by
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz k) (norm_nonneg _))

/-- Pellet's one-zero test, by Rouché against `a₁ (X − c)`. -/
theorem rou_pellet_one_poly (p : ℂ[X]) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (h : rou_pelletTail p c r 1 < ‖(taylor c p).coeff 1‖ * r) :
    rou_discCount p c r = 1 := by
  classical
  set a := (taylor c p).coeff 1 with ha_def
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_mul] at h
    exact (rou_pelletTail_nonneg p c hr.le 1).not_gt h
  have hmem : 1 ∈ Finset.range ((taylor c p).natDegree + 1) := by
    have : 1 ≤ (taylor c p).natDegree := le_natDegree_of_ne_zero ha
    rw [Finset.mem_range]; omega
  have hpq : ∀ z, (p - C a * (X - C c)).eval z =
      ∑ k ∈ (Finset.range ((taylor c p).natDegree + 1)).erase 1,
        (taylor c p).coeff k * (z - c) ^ k := by
    intro z
    rw [eval_sub, rou_eval_eq_sum_taylor p c z, ← Finset.add_sum_erase _ _ hmem]
    simp only [eval_mul, eval_C, eval_sub, eval_X, pow_one, ← ha_def]
    ring
  have hcount := rou_rouche_poly p (C a * (X - C c)) c r fun z hz => by
    rw [mem_sphere, dist_eq_norm] at hz
    rw [hpq]
    refine (rou_norm_sum_erase_le p c z 1 hz.le).trans_lt ?_
    simpa [norm_mul, hz] using h
  rw [hcount, rou_discCount, roots_C_mul _ ha, roots_X_sub_C]
  simp [Multiset.filter_singleton, hr]

/-- Pellet's no-zero test. -/
theorem rou_pellet_zero_poly (p : ℂ[X]) (c : ℂ) (r : ℝ)
    (h : rou_pelletTail p c r 0 < ‖(taylor c p).coeff 0‖) :
    rou_discCount p c r = 0 := by
  classical
  rcases le_or_gt r 0 with hr | hr
  · exact rou_discCount_of_nonpos p c hr
  rw [rou_discCount, Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro z hz hzb
  have h0 : p.eval z = 0 := isRoot_of_mem_roots hz
  have hmem : 0 ∈ Finset.range ((taylor c p).natDegree + 1) := by simp
  rw [rou_eval_eq_sum_taylor p c z, ← Finset.add_sum_erase _ _ hmem, pow_zero, mul_one] at h0
  have hS := rou_norm_sum_erase_le p c z (r := r) 0
    (le_of_lt (by simpa [dist_eq_norm] using hzb))
  rw [eq_neg_of_add_eq_zero_left h0, norm_neg] at h
  linarith

end HodgeLean.Foundations.Program
