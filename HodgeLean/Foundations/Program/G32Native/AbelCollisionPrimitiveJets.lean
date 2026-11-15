import HodgeLean.Foundations.Program.G32Native.AbelCollisionTaylor
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! # Primitive coefficients and the full multiplicity jet -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.G32Native

/-- The retained scalar power-series coefficient has the usual derivative normalization. -/
theorem collision_coefficient_eq_iteratedDeriv {H : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : HasFPowerSeriesAt H p 0) (n : ℕ) :
    p.coeff n = iteratedDeriv n H 0 / (n.factorial : ℂ) := by
  have he := hp.eq_formalMultilinearSeries hp.analyticAt.hasFPowerSeriesAt
  have hc := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q.coeff n) he
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using hc

/-- Vanishing of a normalized primitive coefficient is vanishing of its iterated derivative. -/
theorem collision_coefficient_zero_iff {H : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : HasFPowerSeriesAt H p 0) (n : ℕ) :
    p.coeff n = 0 ↔ iteratedDeriv n H 0 = 0 := by
  rw [collision_coefficient_eq_iteratedDeriv hp n]
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  simp only [div_eq_zero_iff, hf, or_false]

/-- Differentiating the primitive retains every coefficient with its exact multiplicity. -/
theorem collision_primitive_derivative_coefficient {H : ℂ → ℂ}
    {p q : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt H p 0) (hq : HasFPowerSeriesAt (deriv H) q 0) (n : ℕ) :
    q.coeff n = (n + 1 : ℕ) * p.coeff (n + 1) := by
  rw [collision_coefficient_eq_iteratedDeriv hq n,
    collision_coefficient_eq_iteratedDeriv hp (n + 1), iteratedDeriv_succ', Nat.factorial_succ,
    Nat.cast_mul]
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- The primitive coefficients detect the entire order of vanishing of its derivative. -/
theorem collision_primitive_jet_iff {H : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : HasFPowerSeriesAt H p 0) (m : ℕ) :
    (∀ k < m, p.coeff (k + 1) = 0) ↔ (m : ℕ∞) ≤ analyticOrderAt (deriv H) 0 := by
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hp.analyticAt.deriv]
  apply forall_congr'
  intro k
  apply forall_congr'
  intro _
  rw [collision_coefficient_zero_iff hp, iteratedDeriv_succ']

#print axioms collision_coefficient_eq_iteratedDeriv
#print axioms collision_coefficient_zero_iff
#print axioms collision_primitive_derivative_coefficient
#print axioms collision_primitive_jet_iff
end HodgeLean.Foundations.Program.G32Native
