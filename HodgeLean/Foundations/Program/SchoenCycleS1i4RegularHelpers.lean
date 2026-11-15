module

public import HodgeLean.Foundations.Program.SchoenCycleS1i4RecoveryHelpers
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

public section
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
open scoped BigOperators ENNReal
namespace HodgeLean.Foundations.Program

theorem s2e_nonzero_homogeneous_term (m : ℕ) (f : (Fin m → ℂ) → ℂ)
    (p : FormalMultilinearSeries ℂ (Fin m → ℂ) ℂ) (ρ : ℝ≥0∞)
    (hp : HasFPowerSeriesOnBall f p 0 ρ) (hne : ¬ f =ᶠ[nhds 0] 0) :
    ∃ n, s2e_multilinearPolynomial m n (p n) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hne
  filter_upwards [Metric.eball_mem_nhds (0 : Fin m → ℂ) hp.r_pos] with z hz
  have hn (n : ℕ) : p n (fun _ => z) = 0 := by
    rw [s2e_multilinear_diagonal_expansion, h n, map_zero]
  have hs := hp.hasSum hz
  have hs' : HasSum (fun _ : ℕ => (0 : ℂ)) (f z) := by simpa only [hn, zero_add] using hs
  exact hs'.unique hasSum_zero

theorem s2e_line_iteratedDeriv (m : ℕ) (f : (Fin m → ℂ) → ℂ)
    (p : FormalMultilinearSeries ℂ (Fin m → ℂ) ℂ) (ρ : ℝ≥0∞)
    (hp : HasFPowerSeriesOnBall f p 0 ρ) (u : ℂ →L[ℂ] (Fin m → ℂ)) (n : ℕ) :
    iteratedDeriv n (fun t => f (u t)) 0 =
      (n.factorial : ℂ) * p n (fun _ => u 1) := by
  have hp' : HasFPowerSeriesOnBall f p (u 0) ρ := by simpa using hp
  have h := hp'.compContinuousLinearMap
  have hd := h.factorial_smul 1 n
  rw [← iteratedDeriv_eq_iteratedFDeriv] at hd
  simpa only [Function.comp_def, FormalMultilinearSeries.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, nsmul_eq_mul] using hd.symm

end HodgeLean.Foundations.Program
