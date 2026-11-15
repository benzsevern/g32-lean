import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Source: Forster, Lectures on Riemann Surfaces, §10, uniqueness of scalar linear differential equations. -/
theorem logarithmicSolutions_differ_by_constant
    {S : Set ℂ} (hS : IsOpen S) (hc : IsPreconnected S)
    {a F G : ℂ → ℂ} (hF : ∀ z ∈ S, HasDerivAt F (a z * F z) z)
    (hG : ∀ z ∈ S, HasDerivAt G (a z * G z) z)
    (hGn : ∀ z ∈ S, G z ≠ 0) {z₀ : ℂ} (hz₀ : z₀ ∈ S) (hFn : F z₀ ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z ∈ S, F z = c * G z := by
  have hd (z : ℂ) (hz : z ∈ S) : HasDerivAt (fun t => F t / G t) 0 z := by
    convert (hF z hz).div (hG z hz) (hGn z hz) using 1
    ring
  obtain ⟨c, hc⟩ := hS.exists_is_const_of_deriv_eq_zero hc
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv)
  have he (z : ℂ) (hz : z ∈ S) : F z = c * G z :=
    (div_eq_iff (hGn z hz)).mp (hc z hz)
  refine ⟨c, ?_, he⟩
  intro hz
  exact hFn (by simpa only [hz, zero_mul] using he z₀ hz₀)

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
