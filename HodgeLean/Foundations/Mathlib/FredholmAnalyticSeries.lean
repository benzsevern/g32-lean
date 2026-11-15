module

public import Mathlib

/-! # Analyticity of a vector-valued power series with a summable majorant -/

@[expose] public noncomputable section

open Set Filter Topology

namespace HodgeLean.Foundations

/-- A power series `Σ εᵏ • T k` in a Banach space with `Σ ρᵏ ‖T k‖ < ∞` is summable on the ball of
radius `ρ` and its sum is analytic there. -/
theorem b63r_powSeries_analytic {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] (T : ℕ → X) (ρ : ℝ) (hρ : 0 < ρ) (hc : Summable fun k ↦ ρ ^ k * ‖T k‖) :
    (∀ ε ∈ Metric.ball (0 : ℂ) ρ, Summable fun k ↦ ε ^ k • T k) ∧
      AnalyticOnNhd ℂ (fun ε : ℂ ↦ ∑' k, ε ^ k • T k) (Metric.ball (0 : ℂ) ρ) := by
  let p : FormalMultilinearSeries ℂ ℂ X :=
    fun k => ContinuousMultilinearMap.mkPiRing ℂ (Fin k) (T k)
  have hp : ∀ k (y : ℂ), p k (fun _ => y) = y ^ k • T k := by
    intro k y
    simp [p, ContinuousMultilinearMap.mkPiRing_apply]
  have hsum : Summable fun k => ‖p k‖ * ((ρ.toNNReal : NNReal) : ℝ) ^ k := by
    refine hc.congr fun k => ?_
    simp only [p, ContinuousMultilinearMap.norm_mkPiRing, Real.coe_toNNReal _ hρ.le]
    ring
  have hrad : ENNReal.ofReal ρ ≤ p.radius := p.le_radius_of_summable hsum
  have hpos : 0 < p.radius := lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hρ) hrad
  have hfp := p.hasFPowerSeriesOnBall hpos
  have hball : ∀ ε ∈ Metric.ball (0 : ℂ) ρ, ε ∈ Metric.eball (0 : ℂ) p.radius := by
    intro ε hε
    refine lt_of_lt_of_le ?_ hrad
    rw [Metric.mem_ball, dist_zero_right] at hε
    rw [edist_zero_right, ← ofReal_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff hρ).mpr hε
  have hsumε : ∀ ε ∈ Metric.ball (0 : ℂ) ρ,
      HasSum (fun k ↦ ε ^ k • T k) (p.sum ε) := by
    intro ε hε
    have := hfp.hasSum (y := ε) (hball ε hε)
    simpa [hp] using this
  refine ⟨fun ε hε => (hsumε ε hε).summable, fun ε hε => ?_⟩
  have h1 : AnalyticAt ℂ p.sum ε := by
    have := hfp.analyticAt_of_mem (hball ε hε)
    simpa using this
  refine h1.congr ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds hε] with x hx
  exact ((hsumε x hx).tsum_eq).symm

end HodgeLean.Foundations
