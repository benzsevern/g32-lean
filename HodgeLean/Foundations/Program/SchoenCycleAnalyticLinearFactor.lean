import HodgeLean.Foundations.Program.SchoenCycleNativeAnalyticGerms

/-! # Linear factorization of an analytic germ vanishing at the origin -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- An analytic function near the origin is its constant term plus an
analytic family of continuous linear maps evaluated on the coordinate.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 6;
Mathlib, FormalMultilinearSeries.shift and HasFPowerSeriesOnBall.unshift. -/
theorem s2e_analytic_linear_factor (d : ℕ) (f : (Fin d → ℂ) → ℂ)
    (hf : AnalyticAt ℂ f 0) :
    ∃ L : (Fin d → ℂ) → ((Fin d → ℂ) →L[ℂ] ℂ), AnalyticAt ℂ L 0 ∧
      f =ᶠ[nhds 0] (fun z => f 0 + L z z) := by
  obtain ⟨p, hp⟩ := hf
  have hs := p.shift.hasFPowerSeriesOnBall (by
    rw [FormalMultilinearSeries.radius_shift]
    exact hp.radius_pos)
  have he : p.shift.unshift (f 0) = p := by
    funext n
    cases n with
    | zero =>
      ext v
      simpa [FormalMultilinearSeries.unshift] using (hp.coeff_zero v).symm
    | succ n =>
      exact (continuousMultilinearCurryRightEquiv' ℂ n (Fin d → ℂ) ℂ).symm_apply_apply (p (n + 1))
  have hu := hs.unshift (z := f 0)
  rw [he] at hu
  refine ⟨p.shift.sum, hs.analyticAt, ?_⟩
  filter_upwards [hp.eventually_hasSum, hu.hasFPowerSeriesAt.eventually_hasSum] with z hz hz'
  simpa only [zero_add, sub_zero] using hz.unique hz'

#print axioms s2e_analytic_linear_factor
/-- An analytic function is its value at zero plus a sum of coordinates
with analytic coefficients.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 6. -/
theorem s2e_analytic_coordinate_factor (d : ℕ) (f : (Fin d → ℂ) → ℂ)
    (hf : AnalyticAt ℂ f 0) :
    ∃ g : Fin d → (Fin d → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (g i) 0) ∧
      f =ᶠ[nhds 0] (fun z => f 0 + ∑ i, z i * g i z) := by
  obtain ⟨L, hL, he⟩ := s2e_analytic_linear_factor d f hf
  refine ⟨fun i z => L z (Pi.single i 1), ?_, ?_⟩
  · intro i
    exact ((ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1)).analyticAt (L 0)).comp hL
  · filter_upwards [he] with z hz
    rw [hz]
    congr 1
    have hz' : z = ∑ i : Fin d, z i • Pi.single i (1 : ℂ) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    calc
      L z z = L z (∑ i : Fin d, z i • Pi.single i (1 : ℂ)) := congrArg (L z) hz'
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

#print axioms s2e_analytic_coordinate_factor
end HodgeLean.Foundations.Program
