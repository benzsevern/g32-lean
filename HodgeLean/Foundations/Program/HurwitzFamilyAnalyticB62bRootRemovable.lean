import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bBranchRoot
import Mathlib.Analysis.Analytic.IsolatedZeros

noncomputable section
open Filter
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

theorem b6a_contDiffAt_complex_root (r : ℂ → ℂ) (x : ℂ) (e : ℕ) (he : 0 < e)
    (hr : ∀ᶠ z in 𝓝 x, ContinuousAt r z)
    (hp : ContDiffAt ℂ ω (fun z ↦ r z ^ e) x) : ContDiffAt ℂ ω r x := by
  rcases hp.analyticAt.eventually_eq_zero_or_eventually_ne_zero with hz | hn
  · apply contDiffAt_const.congr_of_eventuallyEq
    exact hz.mono fun z hz ↦ (pow_eq_zero_iff he.ne').mp hz
  · apply AnalyticAt.contDiffAt
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [hn, hr.filter_mono nhdsWithin_le_nhds,
        hp.analyticAt.eventually_analyticAt.filter_mono nhdsWithin_le_nhds] with z hz hrc hpa
      have hne : r z ≠ 0 := fun h ↦ hz (by simp [h, he.ne'])
      exact (b6a_contDiffAt_of_pow r z e he hrc hne hpa.contDiffAt).differentiableAt (by simp)
    · exact hr.self_of_nhds

theorem b6a_root_exponent_eq_one (r h : ℂ → ℂ) (x d : ℂ) (e : ℕ) (he : 0 < e)
    (hr : ∀ᶠ z in 𝓝 x, ContinuousAt r z) (hz : r x = 0)
    (hh : ContDiffAt ℂ ω h x) (hd : HasDerivAt h d x) (hne : d ≠ 0)
    (hp : ∀ᶠ z in 𝓝 x, r z ^ e = h z) : e = 1 := by
  have hroot : ContDiffAt ℂ ω r x :=
    b6a_contDiffAt_complex_root r x e he hr (hh.congr_of_eventuallyEq hp)
  have hdr := (hroot.differentiableAt (by simp)).hasDerivAt.pow e
  have heq : (e : ℂ) * r x ^ (e - 1) * deriv r x = d :=
    (hdr.congr_of_eventuallyEq (hp.mono fun _ h ↦ h.symm)).unique hd
  by_contra h
  have hep : e - 1 ≠ 0 := by omega
  rw [hz, zero_pow hep, mul_zero, zero_mul] at heq
  exact hne heq.symm

end HodgeLean.Foundations.Program
