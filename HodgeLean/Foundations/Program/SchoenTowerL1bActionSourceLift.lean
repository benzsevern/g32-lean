import HodgeLean.Foundations.Program.SchoenTowerL1bActionPrimitiveDeck
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp

noncomputable section
set_option maxHeartbeats 200000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- The logarithmic source lift selected by a prescribed nonzero tangent scalar. -/
def s2v_l1b_action_sourceLift (f : ℂ → ℂ) (a w : ℂ) : ℂ :=
  w + a + Complex.log (f (Complex.exp w) / (Complex.exp a * Complex.exp w))

/-- The selected logarithmic source lift projects to the actual source map
where that map has nonzero value. -/
theorem s2v_l1b_action_sourceLift_exp
    (f : ℂ → ℂ) (a w : ℂ) (hn : f (Complex.exp w) ≠ 0) :
    Complex.exp (s2v_l1b_action_sourceLift f a w) = f (Complex.exp w) := by
  rw [s2v_l1b_action_sourceLift, Complex.exp_add, Complex.exp_add,
    Complex.exp_log (div_ne_zero hn (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)))]
  field_simp

/-- The selected source lift commutes with a primitive deck translation. -/
theorem s2v_l1b_action_sourceLift_deck
    (f : ℂ → ℂ) (a w : ℂ) :
    s2v_l1b_action_sourceLift f a (w + 2 * Real.pi * Complex.I) =
      s2v_l1b_action_sourceLift f a w + 2 * Real.pi * Complex.I := by
  simp only [s2v_l1b_action_sourceLift, Complex.exp_add,
    Complex.exp_two_pi_mul_I, mul_one]
  ring

/-- The prescribed nonzero derivative makes the logarithmic correction
tend to zero on the punctured source neighborhood. -/
theorem s2v_l1b_action_source_log_correction_tendsto
    (f : ℂ → ℂ) (a : ℂ) (hfzero : f 0 = 0)
    (hf : HasDerivAt f (Complex.exp a) 0) :
    Filter.Tendsto (fun z : ℂ => Complex.log (f z / (Complex.exp a * z)))
      (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds 0) := by
  have hs : Filter.Tendsto (fun z : ℂ => f z / (Complex.exp a * z))
      (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds (1 : ℂ)) := by
    convert hf.tendsto_slope_zero.div_const (Complex.exp a) using 1
    · funext z
      simp only [zero_add, hfzero, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
      ring
    · simp only [div_self (Complex.exp_ne_zero _)]
  have hc := (continuousAt_clog (by simp : (1 : ℂ) ∈ Complex.slitPlane)).tendsto.comp hs
  simpa only [Function.comp_def, Complex.log_one] using hc

/-- The derivative normalizes the punctured source ratio to a function
tending to one. -/
theorem s2v_l1b_action_source_normalized_ratio_tendsto
    (f : ℂ → ℂ) (a : ℂ) (hfzero : f 0 = 0)
    (hf : HasDerivAt f (Complex.exp a) 0) :
    Filter.Tendsto (fun z : ℂ => f z / (Complex.exp a * z))
      (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds (1 : ℂ)) := by
  convert hf.tendsto_slope_zero.div_const (Complex.exp a) using 1
  · funext z
    simp only [zero_add, hfzero, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
    ring
  · simp only [div_self (Complex.exp_ne_zero _)]

/-- The nonzero derivative prevents further source zeros sufficiently
near the puncture. -/
theorem s2v_l1b_action_source_eventually_ne_zero
    (f : ℂ → ℂ) (a : ℂ) (hfzero : f 0 = 0)
    (hf : HasDerivAt f (Complex.exp a) 0) :
    ∀ᶠ z : ℂ in nhdsWithin 0 ({0}ᶜ : Set ℂ), f z ≠ 0 := by
  have hs := s2v_l1b_action_source_normalized_ratio_tendsto f a hfzero hf
  have hn := hs.eventually (eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0))
  filter_upwards [hn] with z hz hfz
  apply hz
  rw [hfz, zero_div]

end HodgeLean.Foundations.Program
