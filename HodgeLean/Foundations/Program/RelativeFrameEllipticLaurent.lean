import HodgeLean.Foundations.Program.RelativeFrameEllipticResidue
import HodgeLean.Ported.LeanCA.ComplexAnalysis.LaurentSeries.Basic

/-! # A genus-one witness: Laurent parts of a bounded function on the annulus
For `f` holomorphic and bounded by `M` on `A = {1/5 < |u| < 2/5}`, with Laurent coefficients `aₖ`
(`Complex.circleLaurentCoeff`, independent of the radius in `(1/5, 2/5)`): the regular part
`f₊ = Σ_{n ≥ 0} aₙ uⁿ` is holomorphic and bounded by `7M` on `D(0, 2/5)`, the principal part
`f₋ = Σ_{n ≥ 1} a₋ₙ u⁻ⁿ` is holomorphic and bounded by `8M` on `|u| > 1/5`, `f = f₊ + f₋` on `A`,
and the tail `f₋ − a₋₁ u⁻¹ − a₋₂ u⁻²` is `O(|u|⁻³)` on `|u| > 1/5`.
-/

noncomputable section
open Set Filter Topology
namespace HodgeLean.Foundations.Program

/-- A geometric bound gives summability and a bound on the sum. -/
theorem rfw_geom {f : ℕ → ℂ} {C q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (h : ∀ n, ‖f n‖ ≤ C * q ^ n) : Summable f ∧ ‖∑' n, f n‖ ≤ C * (1 - q)⁻¹ :=
  ⟨Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hq1).mul_left C) h,
    tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hq0 hq1).mul_left C) h⟩

/-- The Laurent coefficients on the circle of radius `3/10`. -/
def rfw_lc (fx : ℂ → ℂ) (k : ℤ) : ℂ := Complex.circleLaurentCoeff fx (3 / 10) k

/-- The regular part `Σ_{n ≥ 0} aₙ zⁿ`. -/
def rfw_fp (fx : ℂ → ℂ) (z : ℂ) : ℂ := ∑' n : ℕ, rfw_lc fx n * z ^ n

/-- The principal part `Σ_{n ≥ 0} a₋ₙ₋₁ z⁻ⁿ⁻¹`. -/
def rfw_fm (fx : ℂ → ℂ) (z : ℂ) : ℂ := ∑' n : ℕ, rfw_lc fx (-((n : ℤ) + 1)) * z⁻¹ ^ (n + 1)

/-- The tail `Σ_{n ≥ 0} a₋ₙ₋₃ z⁻ⁿ⁻³` of the principal part. -/
def rfw_f3 (fx : ℂ → ℂ) (z : ℂ) : ℂ := ∑' n : ℕ, rfw_lc fx (-((n : ℤ) + 3)) * z⁻¹ ^ (n + 3)

theorem rfw_annulus_isOpen : IsOpen (b63r_annulus 1 (1 / 5)) := rf4_annulus_isOpen 1 _

section
variable {fx : ℂ → ℂ} {M : ℝ} (hfx : DifferentiableOn ℂ fx (b63r_annulus 1 (1 / 5)))
  (hM : ∀ u ∈ b63r_annulus 1 (1 / 5), ‖fx u‖ ≤ M)
include hfx

theorem rfw_analytic_ring {r R : ℝ} (hr : 1 / 5 < r) (hR : R < 2 / 5) :
    AnalyticOnNhd ℂ fx (Metric.closedBall 0 R \ Metric.ball 0 r) := by
  refine (hfx.analyticOnNhd rfw_annulus_isOpen).mono fun w hw ↦ ?_
  obtain ⟨h1, h2⟩ := hw
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  rw [Metric.mem_ball, dist_zero_right, not_lt] at h2
  exact rfw_mem_annulus (by linarith) (by linarith)

theorem rfw_lc_eq {r : ℝ} (h1 : 1 / 5 < r) (h2 : r < 2 / 5) :
    Complex.circleLaurentCoeff fx r = rfw_lc fx := by
  unfold rfw_lc
  rcases le_total r (3 / 10) with h | h
  · exact (Complex.circleLaurentCoeff_eq_of_analyticOnNhd_annulus (by linarith) h
      (rfw_analytic_ring hfx h1 (by norm_num))).symm
  · exact Complex.circleLaurentCoeff_eq_of_analyticOnNhd_annulus (by norm_num) h
      (rfw_analytic_ring hfx (by norm_num) h2)

include hM

theorem rfw_lc_bound {r : ℝ} (h1 : 1 / 5 < r) (h2 : r < 2 / 5) (k : ℤ) :
    ‖rfw_lc fx k‖ ≤ M * r ^ (-k) := by
  rw [← rfw_lc_eq hfx h1 h2]
  refine Complex.norm_circleLaurentCoeff_le (by linarith) (fun w hw ↦ hM w ?_) k
  have hw' : ‖w‖ = r := mem_sphere_zero_iff_norm.mp hw
  exact rfw_mem_annulus (by linarith) (by linarith)

theorem rfw_term_nat {R t : ℝ} (h1 : 1 / 5 < R) (h2 : R < 2 / 5) (_ht : 0 ≤ t) {z : ℂ}
    (hz : ‖z‖ ≤ t) (n : ℕ) : ‖rfw_lc fx n * z ^ n‖ ≤ M * (t / R) ^ n := by
  have hR : 0 < R := by linarith
  have hb := rfw_lc_bound hfx hM h1 h2 n
  rw [zpow_neg, zpow_natCast] at hb
  rw [norm_mul, norm_pow, div_pow]
  calc ‖rfw_lc fx n‖ * ‖z‖ ^ n ≤ M * (R ^ n)⁻¹ * t ^ n :=
        mul_le_mul hb (pow_le_pow_left₀ (norm_nonneg _) hz n) (by positivity)
          (le_trans (norm_nonneg _) hb)
    _ = M * (t ^ n / R ^ n) := by ring

theorem rfw_term_neg {r t : ℝ} (h1 : 1 / 5 < r) (h2 : r < 2 / 5) (hrt : r ≤ t) {z : ℂ}
    (hz : t ≤ ‖z‖) (n : ℕ) :
    ‖rfw_lc fx (-((n : ℤ) + 1)) * z⁻¹ ^ (n + 1)‖ ≤ M * (r / t) ^ n := by
  have hr : 0 < r := by linarith
  have ht : 0 < t := by linarith
  have hb := rfw_lc_bound hfx hM h1 h2 (-((n : ℤ) + 1))
  rw [neg_neg, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast] at hb
  have hq : r / t ≤ 1 := (div_le_one ht).mpr hrt
  have hz' : ‖z⁻¹‖ ≤ t⁻¹ := by
    rw [norm_inv]; exact inv_anti₀ ht hz
  rw [norm_mul, norm_pow]
  calc ‖rfw_lc fx (-((n : ℤ) + 1))‖ * ‖z⁻¹‖ ^ (n + 1) ≤ M * r ^ (n + 1) * t⁻¹ ^ (n + 1) :=
        mul_le_mul hb (pow_le_pow_left₀ (norm_nonneg _) hz' _) (by positivity)
          (le_trans (norm_nonneg _) hb)
    _ = M * (r / t) ^ (n + 1) := by rw [div_pow, div_eq_mul_inv, inv_pow]; ring
    _ ≤ M * (r / t) ^ n := by
      have h0 : 0 ≤ M := le_trans (norm_nonneg _) (rfw_lc_bound hfx hM h1 h2 0 |>.trans_eq
        (by simp))
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by positivity) hq (by omega)) h0

/-- The regular part is summable and bounded by `7M` on `|z| ≤ 3/10`. -/
theorem rfw_fp_small {z : ℂ} (hz : ‖z‖ ≤ 3 / 10) :
    Summable (fun n : ℕ ↦ rfw_lc fx n * z ^ n) ∧ ‖rfw_fp fx z‖ ≤ 7 * M := by
  have h := rfw_geom (by norm_num) (by norm_num)
    (rfw_term_nat hfx hM (R := 7 / 20) (by norm_num) (by norm_num) (by norm_num) hz)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  norm_num; ring

/-- The principal part is summable and bounded by `6M` on `|z| ≥ 3/10`. -/
theorem rfw_fm_large {z : ℂ} (hz : 3 / 10 ≤ ‖z‖) :
    Summable (fun n : ℕ ↦ rfw_lc fx (-((n : ℤ) + 1)) * z⁻¹ ^ (n + 1)) ∧
      ‖rfw_fm fx z‖ ≤ 6 * M := by
  have h := rfw_geom (by norm_num) (by norm_num)
    (rfw_term_neg hfx hM (r := 1 / 4) (by norm_num) (by norm_num) (by norm_num) hz)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  norm_num; ring

theorem rfw_fp_summable {z : ℂ} (hz : ‖z‖ < 2 / 5) :
    Summable (fun n : ℕ ↦ rfw_lc fx n * z ^ n) := by
  set R := (max ‖z‖ (1 / 4) + 2 / 5) / 2
  have hm : ‖z‖ ≤ max ‖z‖ (1 / 4) := le_max_left _ _
  have hm2 : max ‖z‖ (1 / 4) < 2 / 5 := max_lt hz (by norm_num)
  have hm3 : (1 / 4 : ℝ) ≤ max ‖z‖ (1 / 4) := le_max_right _ _
  have hR1 : 1 / 5 < R := by simp only [R]; linarith
  have hR2 : R < 2 / 5 := by simp only [R]; linarith
  have hmR : max ‖z‖ (1 / 4) < R := by simp only [R]; linarith
  exact (rfw_geom (by positivity) ((div_lt_one (by linarith)).mpr hmR)
    (rfw_term_nat hfx hM hR1 hR2 (by positivity) hm)).1

theorem rfw_fm_summable {z : ℂ} (hz : 1 / 5 < ‖z‖) :
    Summable (fun n : ℕ ↦ rfw_lc fx (-((n : ℤ) + 1)) * z⁻¹ ^ (n + 1)) := by
  set s := min ‖z‖ (3 / 10)
  have hs1 : 1 / 5 < s := lt_min hz (by norm_num)
  have hs2 : s ≤ ‖z‖ := min_le_left _ _
  have hs3 : s ≤ 3 / 10 := min_le_right _ _
  set r := (1 / 5 + s) / 2
  have hr1 : 1 / 5 < r := by simp only [r]; linarith
  have hr2 : r < 2 / 5 := by simp only [r]; linarith
  have hrs : r < s := by simp only [r]; linarith
  exact (rfw_geom (by positivity) ((div_lt_one (by linarith)).mpr hrs)
    (rfw_term_neg hfx hM hr1 hr2 hrs.le hs2)).1

/-- **The Laurent expansion**: `f = f₊ + f₋` on the annulus. -/
theorem rfw_expansion {z : ℂ} (hz : z ∈ b63r_annulus 1 (1 / 5)) :
    fx z = rfw_fp fx z + rfw_fm fx z := by
  obtain ⟨h1, h2⟩ := rfw_annulus_norm hz
  set r := (1 / 5 + ‖z‖) / 2
  set R := (‖z‖ + 2 / 5) / 2
  have hr1 : 1 / 5 < r := by simp only [r]; linarith
  have hr2 : r < 2 / 5 := by simp only [r]; linarith
  have hR1 : 1 / 5 < R := by simp only [R]; linarith
  have hR2 : R < 2 / 5 := by simp only [R]; linarith
  have hS := Complex.hasSum_circleLaurentCoeff_annulus (f := fx) (z := z)
    (by linarith : (0 : ℝ) < r)
    (by simp only [r]; linarith) (by simp only [R]; linarith) (rfw_analytic_ring hfx hr1 hR2)
  rw [rfw_lc_eq hfx hr1 hr2] at hS
  have hA : HasSum (fun n : ℕ ↦ z ^ (n : ℤ) • rfw_lc fx n) (rfw_fp fx z) := by
    have := (rfw_fp_summable hfx hM h2).hasSum
    unfold rfw_fp
    convert this using 2 with n
    rw [zpow_natCast, smul_eq_mul, mul_comm]
  have hB : HasSum (fun n : ℕ ↦ z ^ (-((n : ℤ) + 1)) • rfw_lc fx (-((n : ℤ) + 1)))
      (rfw_fm fx z) := by
    have := (rfw_fm_summable hfx hM h1).hasSum
    unfold rfw_fm
    convert this using 2 with n
    rw [show -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
      smul_eq_mul, mul_comm, inv_pow]
  exact hS.unique (hA.of_nat_of_neg_add_one hB)

/-- The regular part is holomorphic on `D(0, 2/5)`. -/
theorem rfw_fp_differentiableOn : DifferentiableOn ℂ (rfw_fp fx) (Metric.ball 0 (2 / 5)) := by
  intro z₀ hz₀
  rw [mem_ball_zero_iff] at hz₀
  set t := (max ‖z₀‖ (1 / 4) + 2 / 5) / 2
  set R := (t + 2 / 5) / 2
  have hm : ‖z₀‖ ≤ max ‖z₀‖ (1 / 4) := le_max_left _ _
  have hm2 : max ‖z₀‖ (1 / 4) < 2 / 5 := max_lt hz₀ (by norm_num)
  have hm3 : (1 / 4 : ℝ) ≤ max ‖z₀‖ (1 / 4) := le_max_right _ _
  have ht1 : ‖z₀‖ < t := by simp only [t]; linarith
  have ht0 : 0 < t := by simp only [t]; linarith
  have hR1 : 1 / 5 < R := by simp only [R, t]; linarith
  have hR2 : R < 2 / 5 := by simp only [R, t]; linarith
  have htR : t < R := by simp only [R, t]; linarith
  have hd : DifferentiableOn ℂ (rfw_fp fx) (Metric.ball 0 t) :=
    Complex.differentiableOn_tsum_of_summable_norm
      ((summable_geometric_of_lt_one (by positivity)
        ((div_lt_one (by linarith)).mpr htR)).mul_left M)
      (fun n ↦ (differentiable_const _).mul (differentiable_pow n) |>.differentiableOn)
      Metric.isOpen_ball
      (fun n w hw ↦ rfw_term_nat hfx hM hR1 hR2 ht0.le (mem_ball_zero_iff.mp hw).le n)
  exact (hd.differentiableAt (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr ht1)))
    |>.differentiableWithinAt

/-- The principal part is holomorphic on `|z| > 1/5`. -/
theorem rfw_fm_differentiableAt {z₀ : ℂ} (hz₀ : 1 / 5 < ‖z₀‖) :
    DifferentiableAt ℂ (rfw_fm fx) z₀ := by
  set s := min ‖z₀‖ (3 / 10)
  have hs1 : 1 / 5 < s := lt_min hz₀ (by norm_num)
  have hs2 : s ≤ ‖z₀‖ := min_le_left _ _
  have hs3 : s ≤ 3 / 10 := min_le_right _ _
  set t := (1 / 5 + s) / 2
  set r := (1 / 5 + t) / 2
  have ht : t < s := by simp only [t]; linarith
  have hr1 : 1 / 5 < r := by simp only [r, t]; linarith
  have hr2 : r < 2 / 5 := by simp only [r, t]; linarith
  have hrt : r < t := by simp only [r, t]; linarith
  have hU : IsOpen {w : ℂ | t < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hd : DifferentiableOn ℂ (rfw_fm fx) {w : ℂ | t < ‖w‖} :=
    Complex.differentiableOn_tsum_of_summable_norm
      ((summable_geometric_of_lt_one (by positivity)
        ((div_lt_one (by linarith)).mpr hrt)).mul_left M)
      (fun n w hw ↦ by
        have hw0 : w ≠ 0 := by
          rintro rfl; simp only [mem_ofPred_eq, norm_zero] at hw; linarith
        exact ((differentiableAt_const _).mul
          ((differentiableAt_inv hw0).pow _)).differentiableWithinAt)
      hU (fun n w hw ↦ rfw_term_neg hfx hM hr1 hr2 hrt.le (le_of_lt hw) n)
  exact hd.differentiableAt (hU.mem_nhds (by change t < ‖z₀‖; linarith))

/-- The regular part is bounded by `7M` on `D(0, 2/5)`. -/
theorem rfw_fp_bound {z : ℂ} (hz : ‖z‖ < 2 / 5) : ‖rfw_fp fx z‖ ≤ 7 * M := by
  rcases le_or_gt ‖z‖ (3 / 10) with h | h
  · exact (rfw_fp_small hfx hM h).2
  · have hA := rfw_mem_annulus (by linarith) hz
    have he := rfw_expansion hfx hM hA
    have : rfw_fp fx z = fx z - rfw_fm fx z := by rw [he]; ring
    rw [this]
    calc ‖fx z - rfw_fm fx z‖ ≤ ‖fx z‖ + ‖rfw_fm fx z‖ := norm_sub_le _ _
      _ ≤ M + 6 * M := add_le_add (hM z hA) (rfw_fm_large hfx hM h.le).2
      _ = 7 * M := by ring

/-- The principal part is bounded by `8M` on `|z| > 1/5`. -/
theorem rfw_fm_bound {z : ℂ} (hz : 1 / 5 < ‖z‖) : ‖rfw_fm fx z‖ ≤ 8 * M := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (rfw_lc_bound hfx hM (r := 3 / 10)
    (by norm_num) (by norm_num) 0 |>.trans_eq (by simp))
  rcases le_or_gt (3 / 10) ‖z‖ with h | h
  · exact (rfw_fm_large hfx hM h).2.trans (by linarith)
  · have hA := rfw_mem_annulus hz (by linarith)
    have he := rfw_expansion hfx hM hA
    have : rfw_fm fx z = fx z - rfw_fp fx z := by rw [he]; ring
    rw [this]
    calc ‖fx z - rfw_fp fx z‖ ≤ ‖fx z‖ + ‖rfw_fp fx z‖ := norm_sub_le _ _
      _ ≤ M + 7 * M := add_le_add (hM z hA) (rfw_fp_small hfx hM h.le).2
      _ = 8 * M := by ring

/-- The principal part is `a₋₁ z⁻¹ + a₋₂ z⁻² + f₃(z)` on `|z| > 1/5`. -/
theorem rfw_fm_split {z : ℂ} (hz : 1 / 5 < ‖z‖) :
    rfw_fm fx z = rfw_lc fx (-1) * z⁻¹ + rfw_lc fx (-2) * z⁻¹ ^ 2 + rfw_f3 fx z := by
  have h := Summable.sum_add_tsum_nat_add (G := ℂ) 2 (rfw_fm_summable hfx hM hz)
  beta_reduce at h
  have e : ∀ n : ℕ, rfw_lc fx (-(((n + 2 : ℕ) : ℤ) + 1)) * z⁻¹ ^ (n + 2 + 1) =
      rfw_lc fx (-((n : ℤ) + 3)) * z⁻¹ ^ (n + 3) := fun n ↦ by
    rw [show (-(((n + 2 : ℕ) : ℤ) + 1)) = -((n : ℤ) + 3) by push_cast; ring]
  unfold rfw_fm rfw_f3
  rw [← h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    tsum_congr e]
  norm_num

end

end HodgeLean.Foundations.Program
