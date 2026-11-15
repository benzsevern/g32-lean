import HodgeLean.Foundations.Program.RigidStartingSystemDefs
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section
open Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65r_simple_analytic_factor (f : ℂ → ℂ) (a : ℂ)
    (ha : AnalyticAt ℂ f a) (hf0 : f a = 0) (hf1 : deriv f a ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ g a ≠ 0 ∧ ∀ z, f z = (z-a)*g z := by
  let F := fun t : ℂ ↦ f (a+t)
  have hF : AnalyticAt ℂ F 0 := by
    have hh : AnalyticAt ℂ f (a+0) := by simpa only [add_zero] using ha
    exact hh.comp (analyticAt_const.add analyticAt_id)
  obtain ⟨q,hq,heq⟩ := hF.exists_eq_sum_add_pow_mul 2
  have hD : deriv F 0 = deriv f a := by
    simpa only [F,add_zero] using deriv_comp_const_add f a 0
  let g := fun z ↦ deriv f a+(z-a)*q (z-a)
  refine ⟨g,?_,?_,?_⟩
  · have hq' : AnalyticAt ℂ q (a-a) := by simpa only [sub_self] using hq
    have hs : AnalyticAt ℂ (fun z : ℂ ↦ z-a) a := analyticAt_id.sub analyticAt_const
    have hc : AnalyticAt ℂ (fun z ↦ q (z-a)) a := by
      simpa only [Function.comp_def] using hq'.comp (f := fun z : ℂ ↦ z-a) hs
    exact analyticAt_const.add (hs.mul hc)
  · simpa only [g,sub_self,zero_mul,add_zero] using hf1
  · intro z
    have he := heq (z-a)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
      Nat.factorial_one, div_one, pow_zero, pow_one, one_smul,
      iteratedDeriv_zero, iteratedDeriv_one, zero_add, hD] at he
    have he' : f z = (z-a)*deriv f a+(z-a)^2*q (z-a) := by
      simpa only [F,add_sub_cancel,add_zero,hf0,zero_add,smul_eq_mul,Nat.cast_one,div_one,mul_zero] using he
    rw [he']
    dsimp only [g]
    ring

theorem b65r_eventually_ne_punctured (f : ℂ → ℂ) (a : ℂ)
    (ha : AnalyticAt ℂ f a) (hzero : f a = 0 → deriv f a ≠ 0) :
    ∀ᶠ z in 𝓝[≠] a, f z ≠ 0 := by
  by_cases hf : f a = 0
  · obtain ⟨g,hg,hga,hfactor⟩ := b65r_simple_analytic_factor f a ha hf (hzero hf)
    have he : ∀ᶠ z in 𝓝[≠] a, g z ≠ 0 :=
      (hg.continuousAt.eventually_ne hga).filter_mono nhdsWithin_le_nhds
    filter_upwards [he,self_mem_nhdsWithin] with z hz hza
    rw [hfactor]
    exact mul_ne_zero (sub_ne_zero.mpr (by simpa using hza)) hz
  · exact (ha.continuousAt.eventually_ne hf).filter_mono nhdsWithin_le_nhds

theorem b65r_eventually_ne_point (a b : ℂ) : ∀ᶠ z in 𝓝[≠] a, z ≠ b := by
  by_cases h : a = b
  · subst b
    filter_upwards [self_mem_nhdsWithin] with z hz
    simpa using hz
  · exact ((continuousAt_id : ContinuousAt (fun z : ℂ ↦ z) a).eventually_ne h).filter_mono
      nhdsWithin_le_nhds

end HodgeLean.Foundations.Program
