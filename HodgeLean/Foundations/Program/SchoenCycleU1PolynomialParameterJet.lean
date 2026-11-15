import HodgeLean.Foundations.Program.SchoenCycleU1AnalyticPolynomialDivision
import Mathlib.Analysis.Analytic.Polynomial

/-! # Polynomial parameter families and their actual Taylor jets -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- Polynomial evaluation as an actual function analytic at the parameter origin.
Source: Mathlib, `AnalyticAt.aeval_polynomial`. -/
def s2e_u1_polynomialFunction : Polynomial ℂ →+* s2e_u1_analyticFunctionRing where
  toFun p := ⟨fun z => p.eval z, by
    change AnalyticAt ℂ (fun z => p.eval z) 0
    simpa only [Polynomial.coe_aeval_eq_eval, id_eq] using
      (analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) 0).aeval_polynomial p⟩
  map_zero' := by ext z; simp
  map_one' := by ext z; simp
  map_add' p q := by ext z; simp
  map_mul' p q := by ext z; simp

/-- The actual Taylor jet of a polynomial parameter is its algebraic
substitution at the dual-number parameter ε.
Source: Hartshorne, Algebraic Geometry, II.8, polynomial tangent vectors;
Mathlib, `Polynomial.ringHom_ext`. -/
theorem s2e_u1_polynomialFunction_jet :
    s2e_u1_analyticGermJet.comp
      (s2e_u1_analyticFunctionGerm.comp s2e_u1_polynomialFunction) =
        (Polynomial.aeval (TrivSqZeroExt.inr (1 : ℂ))).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    change s2e_u1_analyticGermJet (s2e_u1_analyticGerm
      (fun z => (Polynomial.C a).eval z) (s2e_u1_polynomialFunction (Polynomial.C a)).property) = _
    rw [s2e_u1_analyticGermJet_representative]
    simp only [Polynomial.eval_C, deriv_const, TrivSqZeroExt.inr_zero, add_zero,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C,
      TrivSqZeroExt.algebraMap_eq_inl]
  · change s2e_u1_analyticGermJet (s2e_u1_analyticGerm
      (fun z => (Polynomial.X : Polynomial ℂ).eval z)
      (s2e_u1_polynomialFunction Polynomial.X).property) = _
    rw [s2e_u1_analyticGermJet_representative]
    simp only [Polynomial.eval_X, deriv_id'', TrivSqZeroExt.inl_zero, zero_add,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X]

end HodgeLean.Foundations.Program
