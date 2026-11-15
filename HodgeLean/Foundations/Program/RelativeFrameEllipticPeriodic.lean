import HodgeLean.Foundations.Program.RelativeFrameEllipticLaurent

/-! # A genus-one witness: periodizing the principal part
For `f` bounded holomorphic on the annulus, the tail `f₃ = f₋ − a₋₁ u⁻¹ − a₋₂ u⁻²` is `O(|u|⁻³)`,
so `Φ(z) = Σ_{l ∈ ℤ + iℤ} f₃(z − l)` converges, and `H = Φ + a₋₂ ℘` (Weierstrass `℘` of the
lattice `ℤ + iℤ`, Mathlib `PeriodPair.weierstrassP`) is lattice-periodic, holomorphic and bounded
over the outer region. Near `0`, `H = f₃ + a₋₂ u⁻² + (holomorphic on D(0, 4/5))`, so on the annulus
`H − G = f − a₋₁ u⁻¹` with `G` bounded holomorphic on `D(0, 2/5)`.
-/

noncomputable section
open Set Filter Topology
namespace HodgeLean.Foundations.Program
local instance rfw_decidablePeriodic (p : Prop) : Decidable p := Classical.propDecidable p

/-- The period pair `(1, i)` of `rfw_E`.
Source: Mathlib `PeriodPair`; `Complex.basisOneI`. -/
def rfw_L : PeriodPair where
  ω₁ := 1
  ω₂ := Complex.I
  indep := by
    have h := Complex.basisOneI.linearIndependent
    rw [Complex.coe_basisOneI] at h
    exact h

theorem rfw_mem_lattice {l : ℂ} : l ∈ rfw_L.lattice ↔ ∃ m n : ℤ, l = m + n * Complex.I := by
  rw [PeriodPair.mem_lattice]
  change (∃ m n : ℤ, (m : ℂ) * 1 + n * Complex.I = l) ↔ _
  simp only [mul_one]
  exact ⟨fun ⟨m, n, h⟩ ↦ ⟨m, n, h.symm⟩, fun ⟨m, n, h⟩ ↦ ⟨m, n, h.symm⟩⟩

theorem rfw_lattice_one_le {l : ℂ} (hl : l ∈ rfw_L.lattice) (h0 : l ≠ 0) : 1 ≤ ‖l‖ := by
  obtain ⟨m, n, rfl⟩ := rfw_mem_lattice.mp hl
  exact rfw_lattice_norm h0

theorem rfw_proj_eq_of_mem {z l : ℂ} (hl : l ∈ rfw_L.lattice) : rfw_proj (z + l) = rfw_proj z := by
  obtain ⟨m, n, rfl⟩ := rfw_mem_lattice.mp hl
  exact ((rfw_proj_eq_iff z _).mpr ⟨m, n, by ring⟩).symm

theorem rfw_mem_of_proj_eq {z z' : ℂ} (h : rfw_proj z = rfw_proj z') : z' - z ∈ rfw_L.lattice := by
  obtain ⟨m, n, hmn⟩ := (rfw_proj_eq_iff z z').mp h
  exact rfw_mem_lattice.mpr ⟨m, n, hmn⟩

/-- Every point is a lattice translate of a point of norm less than `4/5`. -/
theorem rfw_reduce (z : ℂ) : ∃ l : rfw_L.lattice, ‖z - l‖ < 4 / 5 := by
  refine ⟨⟨(round z.re : ℂ) + (round z.im : ℂ) * Complex.I,
    rfw_mem_lattice.mpr ⟨_, _, rfl⟩⟩, ?_⟩
  have h1 := abs_sub_round z.re
  have h2 := abs_sub_round z.im
  set w := z - ((round z.re : ℂ) + (round z.im : ℂ) * Complex.I)
  have hre : w.re = z.re - round z.re := by simp [w]
  have him : w.im = z.im - round z.im := by simp [w]
  have hsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h1' : w.re ^ 2 ≤ 1 / 4 := by
    rw [hre]; have := abs_le.mp h1; nlinarith
  have h2' : w.im ^ 2 ≤ 1 / 4 := by
    rw [him]; have := abs_le.mp h2; nlinarith
  change ‖w‖ < 4 / 5
  nlinarith [norm_nonneg w]

/-- Points over the outer region have norm greater than `1/5`. -/
theorem rfw_norm_of_mem_O {z : ℂ} (hz : rfw_proj z ∈ rfw_O) : 1 / 5 < ‖z‖ := by
  by_contra h
  push Not at h
  exact hz ⟨z, by simpa using h, rfl⟩

theorem rfw_not_mem_lattice {z : ℂ} (h1 : 0 < ‖z‖) (h2 : ‖z‖ < 1) : z ∉ rfw_L.lattice := by
  intro hz
  by_cases h0 : z = 0
  · subst h0; simp at h1
  · have := rfw_lattice_one_le hz h0; linarith

theorem rfw_rpow_three (x : ℝ) (hx : 0 ≤ x) : x ^ (-3 : ℝ) = (x ^ 3)⁻¹ := by
  rw [Real.rpow_neg hx, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

section
variable {fx : ℂ → ℂ} {M : ℝ} (hfx : DifferentiableOn ℂ fx (b63r_annulus 1 (1 / 5)))
  (hM : ∀ u ∈ b63r_annulus 1 (1 / 5), ‖fx u‖ ≤ M)
include hfx hM

omit hfx in
theorem rfw_M_nonneg : 0 ≤ M :=
  le_trans (norm_nonneg _) (hM (3 / 10) (by constructor <;> norm_num [Complex.norm_div]))

/-- The tail `f₃` is holomorphic on `|z| > 1/5`. -/
theorem rfw_f3_differentiableAt {z₀ : ℂ} (hz₀ : 1 / 5 < ‖z₀‖) :
    DifferentiableAt ℂ (rfw_f3 fx) z₀ := by
  have hz0 : z₀ ≠ 0 := by rintro rfl; norm_num at hz₀
  have hd : DifferentiableAt ℂ (fun z ↦ rfw_fm fx z - rfw_lc fx (-1) * z⁻¹ -
      rfw_lc fx (-2) * z⁻¹ ^ 2) z₀ :=
    ((rfw_fm_differentiableAt hfx hM hz₀).sub ((differentiableAt_const _).mul
      (differentiableAt_inv hz0))).sub ((differentiableAt_const _).mul
      ((differentiableAt_inv hz0).pow 2))
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz₀] with z hz
  rw [rfw_fm_split hfx hM hz]
  ring

/-- The tail `f₃` is `O(|z|⁻³)` on `|z| > 1/5`. -/
theorem rfw_f3_bound : ∃ K, 0 ≤ K ∧ ∀ z : ℂ, 1 / 5 < ‖z‖ → ‖rfw_f3 fx z‖ ≤ K * (‖z‖ ^ 3)⁻¹ := by
  have hM0 := rfw_M_nonneg hM
  refine ⟨8 * M + 5 * ‖rfw_lc fx (-1)‖ + 25 * ‖rfw_lc fx (-2)‖ + M, by positivity, ?_⟩
  intro z hz
  have hz0 : 0 < ‖z‖ := by linarith
  rcases lt_or_ge ‖z‖ (1 / 2) with h | h
  · have hi : ‖z⁻¹‖ ≤ 5 := by
      rw [norm_inv]
      calc ‖z‖⁻¹ ≤ (1 / 5)⁻¹ := inv_anti₀ (by norm_num) hz.le
        _ = 5 := by norm_num
    have hf3 : rfw_f3 fx z = rfw_fm fx z - rfw_lc fx (-1) * z⁻¹ - rfw_lc fx (-2) * z⁻¹ ^ 2 := by
      rw [rfw_fm_split hfx hM hz]; ring
    have hB : ‖rfw_f3 fx z‖ ≤ 8 * M + 5 * ‖rfw_lc fx (-1)‖ + 25 * ‖rfw_lc fx (-2)‖ := by
      rw [hf3]
      calc _ ≤ ‖rfw_fm fx z‖ + ‖rfw_lc fx (-1) * z⁻¹‖ + ‖rfw_lc fx (-2) * z⁻¹ ^ 2‖ :=
            norm_sub_le_of_le (norm_sub_le _ _) le_rfl
        _ ≤ 8 * M + ‖rfw_lc fx (-1)‖ * 5 + ‖rfw_lc fx (-2)‖ * 5 ^ 2 := by
            rw [norm_mul, norm_mul, norm_pow]
            gcongr
            exact rfw_fm_bound hfx hM hz
        _ = _ := by ring
    have h3 : 1 ≤ (‖z‖ ^ 3)⁻¹ := by
      rw [one_le_inv₀ (by positivity)]
      exact pow_le_one₀ hz0.le (by linarith)
    nlinarith [norm_nonneg (rfw_f3 fx z), norm_nonneg (rfw_lc fx (-1)),
      norm_nonneg (rfw_lc fx (-2))]
  · have hi : ‖z⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      calc ‖z‖⁻¹ ≤ (1 / 2)⁻¹ := inv_anti₀ (by norm_num) h
        _ = 2 := by norm_num
    have hterm : ∀ n : ℕ, ‖rfw_lc fx (-((n : ℤ) + 3)) * z⁻¹ ^ (n + 3)‖ ≤
        (M / 64 * (‖z‖ ^ 3)⁻¹) * (1 / 2) ^ n := by
      intro n
      have hb := rfw_lc_bound hfx hM (r := 1 / 4) (by norm_num) (by norm_num) (-((n : ℤ) + 3))
      rw [neg_neg, show ((n : ℤ) + 3) = ((n + 3 : ℕ) : ℤ) by push_cast; ring, zpow_natCast] at hb
      rw [norm_mul, norm_pow, pow_add, norm_inv, inv_pow (‖z‖) 3]
      have hzn : ‖z‖⁻¹ ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by positivity) (by rwa [← norm_inv]) n
      calc ‖rfw_lc fx (-((n : ℤ) + 3))‖ * (‖z‖⁻¹ ^ n * (‖z‖ ^ 3)⁻¹)
          ≤ M * (1 / 4) ^ (n + 3) * (2 ^ n * (‖z‖ ^ 3)⁻¹) :=
            mul_le_mul hb (mul_le_mul_of_nonneg_right hzn (by positivity)) (by positivity)
              (by positivity)
        _ = (M / 64 * (‖z‖ ^ 3)⁻¹) * ((1 / 4) ^ n * 2 ^ n) := by ring
        _ = (M / 64 * (‖z‖ ^ 3)⁻¹) * (1 / 2) ^ n := by
            rw [← mul_pow]; norm_num
    have hg := (rfw_geom (by norm_num) (by norm_num) hterm).2
    unfold rfw_f3
    refine hg.trans ?_
    have : 0 ≤ (‖z‖ ^ 3)⁻¹ := by positivity
    nlinarith [norm_nonneg (rfw_lc fx (-1)), norm_nonneg (rfw_lc fx (-2))]

end

/-! ## The lattice sum -/

/-- The lattice sum `Φ(z) = Σ_l f₃(z − l)` of the tail. -/
def rfw_Phi (fx : ℂ → ℂ) (z : ℂ) : ℂ := ∑' l : rfw_L.lattice, rfw_f3 fx (z - l)

/-- The lattice sum without the term at `0`. -/
def rfw_Z (fx : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' l : rfw_L.lattice, if l = 0 then 0 else rfw_f3 fx (z - l)

/-- The periodic function `H = Φ + a₋₂ ℘`. -/
def rfw_H (fx : ℂ → ℂ) (z : ℂ) : ℂ :=
  rfw_Phi fx z + rfw_lc fx (-2) * PeriodPair.weierstrassP rfw_L z

/-- The disc function `G = Z + a₋₂ (℘ − z⁻²) − f₊`. -/
def rfw_G (fx : ℂ → ℂ) (z : ℂ) : ℂ :=
  rfw_Z fx z + rfw_lc fx (-2) * PeriodPair.weierstrassPExcept rfw_L 0 z - rfw_fp fx z

theorem rfw_Phi_add (fx : ℂ → ℂ) (z : ℂ) (l : rfw_L.lattice) :
    rfw_Phi fx (z + l) = rfw_Phi fx z := by
  unfold rfw_Phi
  rw [← (Equiv.addRight l).tsum_eq (fun m : rfw_L.lattice ↦ rfw_f3 fx (z + l - m))]
  congr 1
  funext c
  simp only [Equiv.coe_addRight, Submodule.coe_add]
  ring_nf

theorem rfw_H_add (fx : ℂ → ℂ) (z : ℂ) (l : rfw_L.lattice) : rfw_H fx (z + l) = rfw_H fx z := by
  unfold rfw_H
  rw [rfw_Phi_add, PeriodPair.weierstrassP_add_coe]

theorem rfw_H_proj (fx : ℂ → ℂ) {z z' : ℂ} (h : rfw_proj z = rfw_proj z') :
    rfw_H fx z = rfw_H fx z' := by
  have := rfw_H_add fx z ⟨z' - z, rfw_mem_of_proj_eq h⟩
  simp only [add_sub_cancel] at this
  exact this.symm

theorem rfw_wp_split (z : ℂ) :
    PeriodPair.weierstrassP rfw_L z = PeriodPair.weierstrassPExcept rfw_L 0 z + (z ^ 2)⁻¹ := by
  have := PeriodPair.weierstrassPExcept_add rfw_L (0 : rfw_L.lattice) z
  simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero, one_div] at this
  rw [← this]

theorem rfw_ball_one_sub {w : ℂ} (hw : ‖w‖ < 1) : w ∈ ((rfw_L.lattice : Set ℂ) \ {0})ᶜ := by
  rintro ⟨h1, h2⟩
  have := rfw_lattice_one_le h1 h2
  linarith

theorem rfw_wpe_differentiableOn :
    DifferentiableOn ℂ (PeriodPair.weierstrassPExcept rfw_L 0) (Metric.ball 0 1) :=
  (PeriodPair.differentiableOn_weierstrassPExcept rfw_L 0).mono fun _ hw ↦
    rfw_ball_one_sub (mem_ball_zero_iff.mp hw)

theorem rfw_wpe_bound : ∃ Bp, ∀ w : ℂ, ‖w‖ ≤ 4 / 5 →
    ‖PeriodPair.weierstrassPExcept rfw_L 0 w‖ ≤ Bp := by
  obtain ⟨Bp, hBp⟩ := (isCompact_closedBall (0 : ℂ) (4 / 5)).exists_bound_of_continuousOn
    (rfw_wpe_differentiableOn.continuousOn.mono fun w hw ↦ by
      rw [mem_closedBall_zero_iff] at hw; rw [mem_ball_zero_iff]; linarith)
  exact ⟨Bp, fun w hw ↦ hBp w (mem_closedBall_zero_iff.mpr hw)⟩

theorem rfw_wp_differentiableAt {z : ℂ} (h1 : 0 < ‖z‖) (h2 : ‖z‖ < 1) :
    DifferentiableAt ℂ (PeriodPair.weierstrassP rfw_L) z :=
  (PeriodPair.differentiableOn_weierstrassP rfw_L z (rfw_not_mem_lattice h1 h2)).differentiableAt
    (rfw_L.isClosed_lattice.isOpen_compl.mem_nhds (rfw_not_mem_lattice h1 h2))

section
variable {fx : ℂ → ℂ} {K : ℝ} (hK0 : 0 ≤ K)
  (hK : ∀ z : ℂ, 1 / 5 < ‖z‖ → ‖rfw_f3 fx z‖ ≤ K * (‖z‖ ^ 3)⁻¹)

/-- The summable majorant `125 K |l|⁻³`. -/
def rfw_u (K : ℝ) (l : rfw_L.lattice) : ℝ := 125 * K * ‖l‖ ^ (-3 : ℝ)

theorem rfw_u_summable (K : ℝ) : Summable (rfw_u K) :=
  (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _

include hK0 in
theorem rfw_u_nonneg (l : rfw_L.lattice) : 0 ≤ rfw_u K l := by
  unfold rfw_u
  have := Real.rpow_nonneg (norm_nonneg l) (-3 : ℝ)
  positivity

include hK0 hK in
theorem rfw_far_bound {z : ℂ} (hz : ‖z‖ < 4 / 5) (l : rfw_L.lattice) (hl : l ≠ 0) :
    1 / 5 < ‖z - l‖ ∧ ‖rfw_f3 fx (z - l)‖ ≤ rfw_u K l := by
  have hl0 : (l : ℂ) ≠ 0 := fun h ↦ hl (Subtype.ext h)
  have hl1 : 1 ≤ ‖(l : ℂ)‖ := rfw_lattice_one_le l.2 hl0
  have hn : ‖(l : ℂ)‖ - ‖z‖ ≤ ‖z - l‖ := by
    rw [norm_sub_rev]; exact norm_sub_norm_le _ _
  have hd : ‖(l : ℂ)‖ / 5 ≤ ‖z - l‖ := by linarith
  have h15 : 1 / 5 < ‖z - l‖ := by linarith
  refine ⟨h15, (hK _ h15).trans ?_⟩
  unfold rfw_u
  change K * (‖z - l‖ ^ 3)⁻¹ ≤ 125 * K * ‖(l : ℂ)‖ ^ (-3 : ℝ)
  rw [rfw_rpow_three _ (norm_nonneg _)]
  have hp : 0 < ‖(l : ℂ)‖ / 5 := by positivity
  have := inv_anti₀ (pow_pos hp 3) (pow_le_pow_left₀ hp.le hd 3)
  calc K * (‖z - l‖ ^ 3)⁻¹ ≤ K * ((‖(l : ℂ)‖ / 5) ^ 3)⁻¹ := mul_le_mul_of_nonneg_left this hK0
    _ = 125 * K * (‖(l : ℂ)‖ ^ 3)⁻¹ := by rw [div_pow]; field_simp; norm_num

include hK0 hK in
theorem rfw_Z_term_bound {z : ℂ} (hz : ‖z‖ < 4 / 5) (l : rfw_L.lattice) :
    ‖(if l = 0 then 0 else rfw_f3 fx (z - l))‖ ≤ rfw_u K l := by
  split_ifs with h
  · simpa using rfw_u_nonneg hK0 l
  · exact (rfw_far_bound hK0 hK hz l h).2

include hK0 hK in
theorem rfw_Z_bound {z : ℂ} (hz : ‖z‖ < 4 / 5) : ‖rfw_Z fx z‖ ≤ ∑' l, rfw_u K l :=
  tsum_of_norm_bounded (rfw_u_summable K).hasSum (rfw_Z_term_bound hK0 hK hz)

variable (hf3 : ∀ z : ℂ, 1 / 5 < ‖z‖ → DifferentiableAt ℂ (rfw_f3 fx) z)

include hK0 hK hf3 in
theorem rfw_Z_differentiableOn : DifferentiableOn ℂ (rfw_Z fx) (Metric.ball 0 (4 / 5)) := by
  refine Complex.differentiableOn_tsum_of_summable_norm (rfw_u_summable K) (fun l ↦ ?_)
    Metric.isOpen_ball (fun l w hw ↦ rfw_Z_term_bound hK0 hK (mem_ball_zero_iff.mp hw) l)
  by_cases h : l = 0
  · simp only [h, ↓reduceIte]; exact differentiableOn_const 0
  · simp only [h, ↓reduceIte]
    intro w hw
    have h15 := (rfw_far_bound hK0 hK (mem_ball_zero_iff.mp hw) l h).1
    exact ((hf3 _ h15).comp w (differentiableAt_id.sub_const _)).differentiableWithinAt

include hK0 hK in
theorem rfw_Phi_split {z : ℂ} (hz : ‖z‖ < 4 / 5) : rfw_Phi fx z = rfw_f3 fx z + rfw_Z fx z := by
  have hs : Summable fun l : rfw_L.lattice ↦ rfw_f3 fx (z - l) := by
    refine Summable.of_norm_bounded ((rfw_u_summable K).add
      (hasSum_ite_eq (0 : rfw_L.lattice) ‖rfw_f3 fx z‖).summable) fun l ↦ ?_
    by_cases h : l = 0
    · subst h
      simp only [ZeroMemClass.coe_zero, sub_zero, ↓reduceIte]
      linarith [rfw_u_nonneg hK0 (0 : rfw_L.lattice)]
    · simp only [h, ↓reduceIte, add_zero]
      exact (rfw_far_bound hK0 hK hz l h).2
  unfold rfw_Phi rfw_Z
  rw [hs.tsum_eq_add_tsum_ite 0]
  simp only [ZeroMemClass.coe_zero, sub_zero]

end

/-! ## The periodization -/

section
variable {fx : ℂ → ℂ} {K : ℝ} (hK0 : 0 ≤ K)
  (hK : ∀ z : ℂ, 1 / 5 < ‖z‖ → ‖rfw_f3 fx z‖ ≤ K * (‖z‖ ^ 3)⁻¹)
  (hf3 : ∀ z : ℂ, 1 / 5 < ‖z‖ → DifferentiableAt ℂ (rfw_f3 fx) z)

include hK0 hK in
/-- Near a point of norm in `(1/5, 4/5)`: `H = f₃ + Z + a₋₂ ℘`. -/
theorem rfw_H_near {z : ℂ} (hz : ‖z‖ < 4 / 5) :
    rfw_H fx z = rfw_f3 fx z + rfw_Z fx z + rfw_lc fx (-2) * PeriodPair.weierstrassP rfw_L z := by
  unfold rfw_H
  rw [rfw_Phi_split hK0 hK hz]

include hK0 hK hf3 in
theorem rfw_H_differentiableAt {z : ℂ} (hz : rfw_proj z ∈ rfw_O) :
    DifferentiableAt ℂ (rfw_H fx) z := by
  obtain ⟨l, hl⟩ := rfw_reduce z
  set z' := z - l
  have hp : rfw_proj z' = rfw_proj z := by
    have := rfw_proj_eq_of_mem (z := z') l.2
    rw [sub_add_cancel] at this
    exact this.symm
  have h15 := rfw_norm_of_mem_O (hp ▸ hz)
  have hm : Metric.ball (0 : ℂ) (4 / 5) ∈ 𝓝 z' :=
    Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hl)
  have hd' : DifferentiableAt ℂ (rfw_H fx) z' := by
    have hd : DifferentiableAt ℂ (fun w ↦ rfw_f3 fx w + rfw_Z fx w +
        rfw_lc fx (-2) * PeriodPair.weierstrassP rfw_L w) z' :=
      ((hf3 z' h15).add ((rfw_Z_differentiableOn hK0 hK hf3).differentiableAt hm)).add
        ((differentiableAt_const _).mul (rfw_wp_differentiableAt (by linarith) (by linarith)))
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [hm] with w hw
    exact rfw_H_near hK0 hK (mem_ball_zero_iff.mp hw)
  have he : rfw_H fx = fun w ↦ rfw_H fx (w - l) := by
    funext w
    rw [← rfw_H_add fx (w - l) l, sub_add_cancel]
  rw [he]
  exact hd'.comp z (differentiableAt_id.sub_const _)

include hK0 hK in
theorem rfw_H_bounded : ∃ B, ∀ z, rfw_proj z ∈ rfw_O → ‖rfw_H fx z‖ ≤ B := by
  obtain ⟨Bp, hBp⟩ := rfw_wpe_bound
  refine ⟨125 * K + ∑' l, rfw_u K l + ‖rfw_lc fx (-2)‖ * (Bp + 25), fun z hz ↦ ?_⟩
  obtain ⟨l, hl⟩ := rfw_reduce z
  set z' := z - l
  have hp : rfw_proj z' = rfw_proj z := by
    have := rfw_proj_eq_of_mem (z := z') l.2
    rw [sub_add_cancel] at this
    exact this.symm
  have h15 := rfw_norm_of_mem_O (hp ▸ hz)
  have hHz : rfw_H fx z = rfw_H fx z' := rfw_H_proj fx hp.symm
  rw [hHz, rfw_H_near hK0 hK hl, rfw_wp_split]
  have h1 : ‖rfw_f3 fx z'‖ ≤ 125 * K := by
    refine (hK z' h15).trans ?_
    have : (‖z'‖ ^ 3)⁻¹ ≤ 125 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      calc (125 : ℝ)⁻¹ = (1 / 5) ^ 3 := by norm_num
        _ ≤ ‖z'‖ ^ 3 := pow_le_pow_left₀ (by norm_num) h15.le 3
    nlinarith
  have h2 : ‖(z' ^ 2)⁻¹‖ ≤ 25 := by
    rw [norm_inv, norm_pow, inv_le_comm₀ (by positivity) (by norm_num)]
    calc (25 : ℝ)⁻¹ = (1 / 5) ^ 2 := by norm_num
      _ ≤ ‖z'‖ ^ 2 := pow_le_pow_left₀ (by norm_num) h15.le 2
  have h3 := hBp z' hl.le
  have h4 := rfw_Z_bound hK0 hK hl
  calc ‖rfw_f3 fx z' + rfw_Z fx z' + rfw_lc fx (-2) *
        (PeriodPair.weierstrassPExcept rfw_L 0 z' + (z' ^ 2)⁻¹)‖
      ≤ ‖rfw_f3 fx z'‖ + ‖rfw_Z fx z'‖ + ‖rfw_lc fx (-2)‖ *
        (‖PeriodPair.weierstrassPExcept rfw_L 0 z'‖ + ‖(z' ^ 2)⁻¹‖) := by
        refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ ≤ _ := by gcongr

end

/-- **The periodization**: for `f` bounded holomorphic on the annulus, `f − a₋₁ u⁻¹ = H − G` on
the annulus, with `H` lattice-periodic, holomorphic and bounded over the outer region, and `G`
bounded holomorphic on `D(0, 2/5)`. -/
theorem rfw_periodize {fx : ℂ → ℂ} {M : ℝ}
    (hfx : DifferentiableOn ℂ fx (b63r_annulus 1 (1 / 5)))
    (hM : ∀ u ∈ b63r_annulus 1 (1 / 5), ‖fx u‖ ≤ M) :
    ∃ c : ℂ, ∃ H G : ℂ → ℂ, (∀ z z', rfw_proj z = rfw_proj z' → H z = H z') ∧
      (∀ z, rfw_proj z ∈ rfw_O → DifferentiableAt ℂ H z) ∧
      (∃ B, ∀ z, rfw_proj z ∈ rfw_O → ‖H z‖ ≤ B) ∧
      DifferentiableOn ℂ G (Metric.ball 0 (2 * (1 / 5))) ∧
      (∃ B, ∀ z ∈ Metric.ball (0 : ℂ) (2 * (1 / 5)), ‖G z‖ ≤ B) ∧
      ∀ u ∈ b63r_annulus 1 (1 / 5), fx u - c * u⁻¹ = H u - G u := by
  obtain ⟨K, hK0, hK⟩ := rfw_f3_bound hfx hM
  have hf3 : ∀ z : ℂ, 1 / 5 < ‖z‖ → DifferentiableAt ℂ (rfw_f3 fx) z :=
    fun z hz ↦ rfw_f3_differentiableAt hfx hM hz
  have hb : Metric.ball (0 : ℂ) (2 * (1 / 5)) = Metric.ball 0 (2 / 5) := by norm_num
  obtain ⟨Bp, hBp⟩ := rfw_wpe_bound
  refine ⟨rfw_lc fx (-1), rfw_H fx, rfw_G fx, fun z z' h ↦ rfw_H_proj fx h,
    fun z hz ↦ rfw_H_differentiableAt hK0 hK hf3 hz, rfw_H_bounded hK0 hK, ?_, ?_, ?_⟩
  · rw [hb]
    have h45 : Metric.ball (0 : ℂ) (2 / 5) ⊆ Metric.ball 0 (4 / 5) :=
      Metric.ball_subset_ball (by norm_num)
    have h1 : Metric.ball (0 : ℂ) (2 / 5) ⊆ Metric.ball 0 1 :=
      Metric.ball_subset_ball (by norm_num)
    exact (((rfw_Z_differentiableOn hK0 hK hf3).mono h45).add
      ((rfw_wpe_differentiableOn.mono h1).const_mul _)).sub (rfw_fp_differentiableOn hfx hM)
  · refine ⟨∑' l, rfw_u K l + ‖rfw_lc fx (-2)‖ * Bp + 7 * M, fun z hz ↦ ?_⟩
    rw [hb, mem_ball_zero_iff] at hz
    unfold rfw_G
    calc ‖rfw_Z fx z + rfw_lc fx (-2) * PeriodPair.weierstrassPExcept rfw_L 0 z - rfw_fp fx z‖
        ≤ ‖rfw_Z fx z‖ + ‖rfw_lc fx (-2)‖ * ‖PeriodPair.weierstrassPExcept rfw_L 0 z‖ +
          ‖rfw_fp fx z‖ := by
          refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) le_rfl)
          rw [norm_mul]
      _ ≤ _ := by
          gcongr
          · exact rfw_Z_bound hK0 hK (by linarith)
          · exact hBp z (by linarith)
          · exact rfw_fp_bound hfx hM hz
  · intro u hu
    obtain ⟨h1, h2⟩ := rfw_annulus_norm hu
    have hu0 : u ≠ 0 := by rintro rfl; norm_num at h1
    rw [rfw_expansion hfx hM hu, rfw_fm_split hfx hM h1, rfw_H_near hK0 hK (by linarith),
      rfw_wp_split]
    unfold rfw_G
    field_simp
    ring

end HodgeLean.Foundations.Program
