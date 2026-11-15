import HodgeLean.Foundations.Program.RigidStartingSystemDefs
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

def b65r_localLog (g : ℂ → ℂ) (a z : ℂ) : ℂ :=
  Complex.log (g a)+Complex.log (g z/g a)

theorem b65r_localLog_exp (g : ℂ → ℂ) (a z : ℂ) (ha : g a ≠ 0) (hz : g z ≠ 0) :
    Complex.exp (b65r_localLog g a z) = g z := by
  rw [b65r_localLog, Complex.exp_add, Complex.exp_log ha,
    Complex.exp_log (div_ne_zero hz ha)]
  field_simp

theorem b65r_localLog_analyticAt (g : ℂ → ℂ) (a : ℂ)
    (hg : AnalyticAt ℂ g a) (ha : g a ≠ 0) :
    AnalyticAt ℂ (b65r_localLog g a) a := by
  have hs : g a/g a ∈ Complex.slitPlane := by simp [ha]
  exact analyticAt_const.add ((hg.div analyticAt_const ha).clog hs)

theorem b65r_localLog_hasDerivAt (g : ℂ → ℂ) (a z g' : ℂ)
    (hg : HasDerivAt g g' z) (ha : g a ≠ 0) (hs : g z/g a ∈ Complex.slitPlane) :
    HasDerivAt (b65r_localLog g a) (g'/g z) z := by
  have hh := ((Complex.hasDerivAt_log hs).comp z (hg.div_const (g a))).const_add (Complex.log (g a))
  have hz : g z ≠ 0 := (div_ne_zero_iff.mp (Complex.slitPlane_ne_zero hs)).1
  convert hh using 1
  · rfl
  · field_simp
    <;> ring

theorem b65r_localLog_neighbourhood (g : ℂ → ℂ) (a : ℂ)
    (hg : AnalyticAt ℂ g a) (ha : g a ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ AnalyticOnNhd ℂ g (ball a r) ∧
      (∀ z ∈ ball a r, g z/g a ∈ Complex.slitPlane) ∧
      AnalyticOnNhd ℂ (b65r_localLog g a) (ball a r) := by
  have hs : g a/g a ∈ Complex.slitPlane := by simp [ha]
  have he : ∀ᶠ z in 𝓝 a, g z/g a ∈ Complex.slitPlane :=
    (hg.continuousAt.div_const (g a)).tendsto.eventually (Complex.isOpen_slitPlane.mem_nhds hs)
  obtain ⟨r1,hr1,hsub⟩ := Metric.mem_nhds_iff.mp he
  obtain ⟨r0,hr0,hg0⟩ := hg.exists_ball_analyticOnNhd
  have hm0 : ball a (min r0 r1) ⊆ ball a r0 := ball_subset_ball (min_le_left _ _)
  have hm1 : ball a (min r0 r1) ⊆ ball a r1 := ball_subset_ball (min_le_right _ _)
  refine ⟨min r0 r1, lt_min hr0 hr1, hg0.mono hm0, ?_, ?_⟩
  · intro z hz
    exact hsub (hm1 hz)
  · intro z hz
    exact analyticAt_const.add (((hg0 z (hm0 hz)).div analyticAt_const ha).clog (hsub (hm1 hz)))

end HodgeLean.Foundations.Program
