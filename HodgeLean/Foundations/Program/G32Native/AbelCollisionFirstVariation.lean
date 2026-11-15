import HodgeLean.Foundations.Program.G32Native.AbelCollisionTrace
import HodgeLean.Foundations.Program.G32Native.AbelCollisionPowerLimit
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Scalar first variation along a monic collision path -/
noncomputable section
set_option maxHeartbeats 400000
open Filter
open scoped Topology BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- A root-of-unity path extracts the derivative in one monic coefficient coordinate. -/
theorem monic_root_path_first_variation
    {n : ℕ} (hn : 0 < n) (ζ : Fin n → ℂ)
    (hζ : ∀ i, ζ i ^ n = 1)
    (hmoment : ∀ k, 0 < k → k < n → ∑ i, ζ i ^ k = 0)
    (G H : ℂ → ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hG : DifferentiableAt ℂ G 0) (hH : HasFPowerSeriesAt H p 0)
    (c : ℂ) (he : ∀ᶠ t in 𝓝 (0 : ℂ), G (-(t ^ n)) = (∑ i, H (ζ i * t)) + c) :
    deriv G 0 = -(n : ℂ) * p.coeff n := by
  have h0 : G 0 = (n : ℂ) * H 0 + c := by
    simpa only [zero_pow (Nat.ne_of_gt hn), neg_zero, mul_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using he.self_of_nhds
  have hpath := collision_negative_power_slope_limit hn hG.hasDerivAt
  have htrace := collision_trace_limit hn ζ hζ hmoment hH
  have heq : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      (G (-(t ^ n)) - G 0) / t ^ n =
        ((∑ i, H (ζ i * t)) - (n : ℂ) * H 0) / t ^ n := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds] with t ht
    rw [ht, h0]
    ring
  have hd : -deriv G 0 = (n : ℂ) * p.coeff n :=
    tendsto_nhds_unique (hpath.congr' heq) htrace
  calc
    deriv G 0 = -((n : ℂ) * p.coeff n) := neg_eq_iff_eq_neg.mp hd
    _ = -(n : ℂ) * p.coeff n := (neg_mul _ _).symm

#print axioms monic_root_path_first_variation
end HodgeLean.Foundations.Program.G32Native
