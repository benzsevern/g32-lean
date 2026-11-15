import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.LocalLogarithmicPrimitive
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.LogarithmicSolutionUniqueness
import HodgeLean.Foundations.Program.HurwitzPrymCovConnected

noncomputable section
open HodgeLean.Foundations.Program
open Filter Topology Set Metric
open TauCeti.Contour
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Source: Forster, Lectures on Riemann Surfaces, §§10, 18, regular singular scalar equations. -/
theorem meromorphic_extension_of_logarithmic_equation {a F : ℂ → ℂ}
    (ha : MeromorphicAt a 0) (ho : (-1 : WithTop ℤ) ≤ meromorphicOrderAt a 0)
    (n : ℤ) (hr : residue a 0 = (n : ℂ))
    (hF : ∀ᶠ z in 𝓝[≠] 0, F z ≠ 0 ∧ HasDerivAt F (a z * F z) z) :
    MeromorphicAt F 0 ∧ meromorphicOrderAt F 0 = (n : WithTop ℤ) := by
  obtain ⟨G, hGm, hGo, hG⟩ := meromorphic_logarithmicPrimitive_at_integral_residue ha ho n hr
  have hh : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 →
      (F z ≠ 0 ∧ HasDerivAt F (a z * F z) z) ∧
      (G z ≠ 0 ∧ HasDerivAt G (a z * G z) z) :=
    eventually_nhdsWithin_iff.mp (hF.and hG)
  obtain ⟨r, hr0, hball⟩ := Metric.eventually_nhds_iff.mp hh
  have hS := b4cov_isConnected_ball_diff (F := ℂ) (by
    rw [← Module.finrank_eq_rank]
    norm_num) (0 : ℂ) hr0
  have hloc (z : ℂ) (hz : z ∈ ball (0 : ℂ) r \ {0}) :
      (F z ≠ 0 ∧ HasDerivAt F (a z * F z) z) ∧
      (G z ≠ 0 ∧ HasDerivAt G (a z * G z) z) := by
    exact hball (by simpa only [mem_ball, dist_comm] using hz.1) hz.2
  obtain ⟨z₀, hz₀⟩ := hS.1
  obtain ⟨c, hc, he⟩ := logarithmicSolutions_differ_by_constant
    (isOpen_ball.sdiff isClosed_singleton) hS.2
    (fun z hz => (hloc z hz).1.2) (fun z hz => (hloc z hz).2.2)
    (fun z hz => (hloc z hz).2.1) hz₀ (hloc z₀ hz₀).1.1
  have hb : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ ball (0 : ℂ) r := ball_mem_nhds 0 hr0
  have hev : F =ᶠ[𝓝[≠] 0] (fun z => c * G z) := by
    filter_upwards [hb.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hzr hz0
    exact he z ⟨hzr, hz0⟩
  refine ⟨((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) 0).meromorphicAt.mul hGm).congr hev.symm, ?_⟩
  rw [meromorphicOrderAt_congr hev]
  change meromorphicOrderAt ((fun _ : ℂ => c) * G) 0 = n
  rw [meromorphicOrderAt_mul_of_ne_zero analyticAt_const hc]
  exact hGo

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
