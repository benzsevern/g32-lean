module

public import HodgeLean.Foundations.Program.SchoenCycleS1i4AxisHelpers
public import HodgeLean.Foundations.Program.SchoenCycleS1i4BallHelpers
import all HodgeLean.Foundations.Program.SchoenCycleDivisionCoefficients
import all Mathlib.Basic.Complex.Basic

public section
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
open scoped BigOperators ENNReal NNReal
namespace HodgeLean.Foundations.Program

theorem s2e_recovered_diagonal_subtype (m n : ℕ)
    (p : FormalMultilinearSeries ℂ (Fin m → ℂ) ℂ) (z : Fin m → ℂ) :
    p n (fun _ => z) = ∑' a : {a : Fin m →₀ ℕ // a.degree = n},
      MvPowerSeries.coeff a.val (s2e_recoveredSeries m p) * ∏ i, z i ^ a.val i := by
  classical
  rw [s2e_recovered_diagonal]
  have h := tsum_subtype {a : Fin m →₀ ℕ | a.degree = n}
    (fun a => MvPowerSeries.coeff a (s2e_recoveredSeries m p) * ∏ i, z i ^ a i)
  convert h.symm using 1
  · apply tsum_congr
    intro a
    simp only [Set.indicator, Set.mem_ofPred_eq]
  · rfl

theorem s2e_recovered_germ (d : ℕ) (f : (Fin (d + 1) → ℂ) → ℂ)
    (p : FormalMultilinearSeries ℂ (Fin (d + 1) → ℂ) ℂ) (ρ : ℝ≥0∞)
    (hp : HasFPowerSeriesOnBall f p 0 ρ) (r : Fin (d + 1) → ℝ)
    (hr : ∀ i, 0 < r i)
    (hF : Summable (fun a => ‖MvPowerSeries.coeff a (s2e_recoveredSeries (d + 1) p)‖ *
      s2e_divWeight d r a)) :
    f =ᶠ[nhds 0] s2e_divSeries (d + 1) (s2e_recoveredSeries (d + 1) p) := by
  obtain ⟨q, σ, hq, hdiag⟩ := s2e_monomial_ball_expansion d r hr _ hF
  have hqd (n : ℕ) (z : Fin (d + 1) → ℂ) : q n (fun _ => z) = p n (fun _ => z) := by
    rw [hdiag, s2e_recovered_diagonal_subtype]
  filter_upwards [Metric.eball_mem_nhds (0 : Fin (d + 1) → ℂ) hp.r_pos,
    Metric.eball_mem_nhds (0 : Fin (d + 1) → ℂ) hq.r_pos] with z hz hzq
  have hpz := hp.hasSum hz
  have hqz := hq.hasSum hzq
  simp only [zero_add, hqd] at hpz hqz
  exact hpz.unique hqz

theorem s2e_recovery_small_radii (d : ℕ)
    (p : FormalMultilinearSeries ℂ (Fin (d + 1) → ℂ) ℂ)
    (hpos : 0 < p.radius) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : Fin (d + 1) → ℝ, (∀ i, 0 < r i ∧ r i < ε) ∧
      Summable (fun a => ‖MvPowerSeries.coeff a (s2e_recoveredSeries (d + 1) p)‖ *
        s2e_divWeight d r a) := by
  obtain ⟨R, hR, hRρ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hpos
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hm : (0 : ℝ) < d + 1 := by positivity
  obtain ⟨t, ht, ht'⟩ := exists_between (lt_min hε (div_pos hR' hm))
  let t' : ℝ≥0 := ⟨t, ht.le⟩
  have hmt : (((d + 1 : ℕ) : ℝ≥0) * t' : ℝ≥0∞) < p.radius := by
    apply lt_trans _ hRρ
    have h : ((d + 1 : ℝ≥0) * t' : ℝ≥0) < R := by
      change ((d : ℝ) + 1) * t < (R : ℝ)
      have := (lt_div_iff₀ hm).mp (lt_of_lt_of_le ht' (min_le_right _ _))
      nlinarith
    exact_mod_cast h
  refine ⟨fun _ => t, fun _ => ⟨ht, ht'.trans_le (min_le_left _ _)⟩, ?_⟩
  have hs := s2e_recovered_summable (d + 1) p t' hmt
  convert hs using 1
  funext a
  simp only [s2e_divWeight, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum]
  rfl

end HodgeLean.Foundations.Program
