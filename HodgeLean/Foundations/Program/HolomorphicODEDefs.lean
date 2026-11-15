module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Quantitative data for holomorphic differential equations -/

public section

noncomputable section
open Set Metric
open scoped Interval
namespace HodgeLean.Foundations.Program

/-- A conservative time radius leaving room for variation of the initial value.
Source: Hille, Ordinary Differential Equations in the Complex Domain, §2.3,
Picard iteration with a uniform bound on the vector field. -/
def b65_radius (R S M : ℝ) : ℝ := min (R / 2) (S / (4 * (M + 1)))

example : b65_radius 2 4 1 = 1 / 2 := by norm_num [b65_radius]

/-- A nonconstant rank-one test vector field with a genuine parameter.
Source: the elementary equation y' = p + x. -/
def b65_testField (q : ℂ × (ℂ × ℂ)) : ℂ := q.1 + q.2.1

example : AnalyticOnNhd ℂ b65_testField Set.univ := by
  intro q hq
  exact analyticAt_fst.add (analyticAt_fst.comp analyticAt_snd)

example : b65_testField (1, (1, 0)) ≠ b65_testField (0, (0, 0)) := by
  norm_num [b65_testField]

example : 0 < Module.finrank ℂ ℂ := by simp

example : ∀ q ∈ ball (0 : ℂ) 1 ×ˢ (ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1),
    ‖b65_testField q‖ ≤ (2 : ℝ) := by
  intro q hq
  have hp : ‖q.1‖ < 1 := by simpa [mem_ball, dist_zero_right] using hq.1
  have hx : ‖q.2.1‖ < 1 := by simpa [mem_ball, dist_zero_right] using hq.2.1
  exact (norm_add_le q.1 q.2.1).trans (by linarith)

example : 0 < b65_radius 1 1 2 := by norm_num [b65_radius]

example : ContinuousOn (fun q : ℝ × ℂ ↦ (q.1 : ℂ) * q.2)
    (Set.uIcc (0 : ℝ) 1 ×ˢ Set.univ) := by fun_prop

example (t : ℝ) : AnalyticOnNhd ℂ (fun z : ℂ ↦ (t : ℂ) * z) Set.univ := by
  intro z hz
  exact analyticAt_const.mul analyticAt_id

example : (fun q : ℝ × ℂ ↦ (q.1 : ℂ) * q.2) (1, 1) ≠
    (fun q : ℝ × ℂ ↦ (q.1 : ℂ) * q.2) (0, 1) := by norm_num

end HodgeLean.Foundations.Program
