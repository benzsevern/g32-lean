module

public import HodgeLean.Foundations.Program.SchoenCycleS1i4MultilinearHelpers
public import HodgeLean.Foundations.Program.SchoenCycleS1i4MonomialHelpers
import all HodgeLean.Foundations.Program.SchoenCycleDivisionSeries
import all HodgeLean.Foundations.Program.SchoenCycleDivisionCoefficients

public section
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
open scoped BigOperators ENNReal NNReal
namespace HodgeLean.Foundations.Program

theorem s2e_weight_lower_radius (d : ℕ) (r : Fin (d + 1) → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hr : ∀ i, δ ≤ r i) (a : Fin (d + 1) →₀ ℕ) :
    δ ^ a.degree ≤ s2e_divWeight d r a := by
  rw [Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun _ _ => pow_nonneg hδ _)
    (fun i _ => pow_le_pow_left₀ hδ (hr i) _)

theorem s2e_monomial_ball_expansion
    (d : ℕ) (r : Fin (d + 1) → ℝ) (hr : ∀ i, 0 < r i)
    (F : MvPowerSeries (Fin (d + 1)) ℂ)
    (hF : Summable (fun a => ‖MvPowerSeries.coeff a F‖ * s2e_divWeight d r a)) :
    ∃ p : FormalMultilinearSeries ℂ (Fin (d + 1) → ℂ) ℂ, ∃ ρ : ℝ≥0∞,
      HasFPowerSeriesOnBall (s2e_divSeries (d + 1) F) p 0 ρ ∧
      ∀ n z, p n (fun _ => z) =
        ∑' a : {a : Fin (d + 1) →₀ ℕ // a.degree = n},
          MvPowerSeries.coeff a.val F * ∏ i, z i ^ a.val i := by
  classical
  choose p hp hn using fun n => s2e_homogeneous_multilinear_form (d + 1) n F
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image Finset.univ r
    (show (Finset.univ : Finset (Fin (d + 1))).Nonempty from ⟨Fin.last d, Finset.mem_univ _⟩)
  let δ : ℝ≥0 := ⟨r i, (hr i).le⟩
  have hδ : 0 < δ := hr i
  have hδr (j) : (δ : ℝ) ≤ r j := hmin j (Finset.mem_univ _)
  have hsmall : Summable (fun a => ‖MvPowerSeries.coeff a F‖ * (δ : ℝ) ^ a.degree) :=
    hF.of_nonneg_of_le (fun a => mul_nonneg (norm_nonneg _) (pow_nonneg δ.coe_nonneg _))
      (fun a => mul_le_mul_of_nonneg_left (s2e_weight_lower_radius d r δ δ.coe_nonneg hδr a)
        (norm_nonneg _))
  have hgroup := (hsmall.hasSum.tsum_fiberwise (fun a : Fin (d + 1) →₀ ℕ => a.degree)).summable
  have hpn : Summable (fun n => ‖p n‖ * (δ : ℝ) ^ n) := by
    apply hgroup.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg δ.coe_nonneg _))
    intro n
    calc
      _ ≤ (∑' a : {a : Fin (d + 1) →₀ ℕ // a.degree = n},
          ‖MvPowerSeries.coeff a.val F‖) * (δ : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right (hn n) (pow_nonneg δ.coe_nonneg _)
      _ = _ := by
        rw [← tsum_mul_right]
        apply tsum_congr
        intro a
        rw [a.property]
  refine ⟨p, δ, ⟨FormalMultilinearSeries.le_radius_of_summable_norm p hpn, by exact_mod_cast hδ, ?_⟩, hp⟩
  intro z hz
  have hzδ : ‖z‖ < (δ : ℝ) := by
    have h := mem_eball_zero_iff.mp hz
    exact_mod_cast h
  have hz' (j) : ‖z j‖ ≤ r j := (norm_le_pi_norm z j).trans (hzδ.le.trans (hδr j))
  have hs := (s2e_monomial_norm_summable d r F hF z hz').of_norm
  have hg := hs.hasSum.tsum_fiberwise (fun a : Fin (d + 1) →₀ ℕ => a.degree)
  convert hg using 1
  · funext n
    rw [hp]
    rfl
  · simp only [zero_add]
    rfl

end HodgeLean.Foundations.Program
