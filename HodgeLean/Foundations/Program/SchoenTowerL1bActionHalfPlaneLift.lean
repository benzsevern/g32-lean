import HodgeLean.Foundations.Program.SchoenTowerL1bActionLogLifts
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Tactic.Linarith

noncomputable section
set_option maxHeartbeats 200000
open Set Topology
namespace HodgeLean.Foundations.Program

/-- A continuous punctured-disk map has a continuous logarithmic lift on
the left half-plane covering that disk. -/
theorem s2v_l1b_action_halfplane_log_lift
    (h : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hc : ContinuousOn h (Metric.ball 0 r))
    (hnonzero : ∀ z ∈ Metric.ball (0 : ℂ) r, z ≠ 0 → h z ≠ 0) :
    ∃ L : ℂ → ℂ, ContinuousOn L {z : ℂ | z.re < Real.log r} ∧
      ∀ z : ℂ, z.re < Real.log r → Complex.exp (L z) = h (Complex.exp z) := by
  let U : Set ℂ := {z | z.re < Real.log r}
  have hne : U.Nonempty := by
    refine ⟨((Real.log r - 1 : ℝ) : ℂ), ?_⟩
    change Real.log r - 1 < Real.log r
    linarith
  haveI : ContractibleSpace U := (convex_halfSpace_re_lt (Real.log r)).contractibleSpace hne
  have hsim : IsSimplyConnected U := by
    change SimplyConnectedSpace U
    infer_instance
  have hopen : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  have hexp : MapsTo Complex.exp U (Metric.ball (0 : ℂ) r) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_exp]
    exact (Real.exp_lt_exp.mpr hz).trans_eq (Real.exp_log hr)
  have hcomp : ContinuousOn (fun z => h (Complex.exp z)) U :=
    hc.comp Complex.continuous_exp.continuousOn hexp
  obtain ⟨L, hL, he⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsim hopen hcomp (by
    rintro ⟨z, hz, hzero⟩
    exact hnonzero _ (hexp hz) (Complex.exp_ne_zero _) hzero)
  exact ⟨L, hL, fun z hz => he hz⟩

/-- A local plane homeomorphism fixing zero supplies a punctured disk and
a logarithmic lift on its covering half-plane. -/
theorem s2v_l1b_action_local_homeomorph_log_lift
    (e : OpenPartialHomeomorph ℂ ℂ) (hzero : (0 : ℂ) ∈ e.source) (hezero : e 0 = 0) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : ℂ) r ⊆ e.source ∧
      ∃ L : ℂ → ℂ, ContinuousOn L {z : ℂ | z.re < Real.log r} ∧
        ∀ z : ℂ, z.re < Real.log r → Complex.exp (L z) = e (Complex.exp z) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_source 0 hzero
  have hn : ∀ z ∈ Metric.ball (0 : ℂ) r, z ≠ 0 → e z ≠ 0 := by
    intro z hz hne he
    apply hne
    apply e.injOn (hball hz) hzero
    exact he.trans hezero.symm
  obtain ⟨L, hL, he⟩ := s2v_l1b_action_halfplane_log_lift e r hr
    (e.continuousOn.mono hball) hn
  exact ⟨r, hr, hball, L, hL, he⟩

/-- A logarithmic lift on a half-plane transforms a deck translation by a
constant integer multiple of the target deck translation. -/
theorem s2v_l1b_action_halfplane_deck_coefficient
    (h L : ℂ → ℂ) (b : ℝ)
    (hL : ContinuousOn L {z : ℂ | z.re < b})
    (he : ∀ z : ℂ, z.re < b → Complex.exp (L z) = h (Complex.exp z)) :
    ∃ ε : ℤ, ∀ z : ℂ, z.re < b →
      L (z + 2 * Real.pi * Complex.I) = L z + ε * (2 * Real.pi * Complex.I) := by
  let X := {z : ℂ // z.re < b}
  haveI : PreconnectedSpace X := Subtype.preconnectedSpace
    (convex_halfSpace_re_lt b).isPreconnected
  have hp : (2 * Real.pi * Complex.I).re = 0 := by simp
  let D : X → X := fun z => ⟨z + 2 * Real.pi * Complex.I, by
    change (z.1 + 2 * Real.pi * Complex.I).re < b
    rw [Complex.add_re, hp, add_zero]
    exact z.2⟩
  have hD : Continuous D := (continuous_subtype_val.add continuous_const).subtype_mk _
  have hc : Continuous (fun z : X => L z) := continuousOn_iff_continuous_restrict.mp hL
  have hproj (z : X) : Complex.exp (L (D z)) = Complex.exp (L z) := by
    rw [he _ (D z).2, he _ z.2]
    change h (Complex.exp (z.1 + 2 * Real.pi * Complex.I)) = h (Complex.exp z.1)
    rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  let x₀ : X := ⟨((b - 1 : ℝ) : ℂ), by
    change b - 1 < b
    linarith⟩
  obtain ⟨ε, hε⟩ := s2v_l1b_action_log_lifts_differ_int
    (fun z : X => L (D z)) (fun z : X => L z) (hc.comp hD) hc hproj x₀
  exact ⟨ε, fun z hz => hε ⟨z, hz⟩⟩

end HodgeLean.Foundations.Program
