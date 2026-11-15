import HodgeLean.Foundations.Program.SchoenCycleU1AnalyticJet
import Mathlib.Algebra.Polynomial.Div

/-! # Polynomial divisibility in analytic families and their first jets -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- Functions holomorphic near zero, retained as actual functions.
Source: Mathlib, `AnalyticAt.add`, `AnalyticAt.mul`, and `AnalyticAt.neg`. -/
def s2e_u1_analyticFunctionRing : Subring (ℂ → ℂ) where
  carrier := {f | AnalyticAt ℂ f 0}
  zero_mem' := analyticAt_const
  one_mem' := analyticAt_const
  add_mem' := fun hf hg => hf.add hg
  mul_mem' := fun hf hg => hf.mul hg
  neg_mem' := fun hf => hf.neg

/-- The germ map of actual holomorphic functions.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, analytic local rings. -/
def s2e_u1_analyticFunctionGerm :
    s2e_u1_analyticFunctionRing →+* s2e_u1_analyticGermRing where
  toFun f := s2e_u1_analyticGerm f.val f.property
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- Evaluation of an actual analytic coefficient at a specified parameter.
Source: Mathlib, `Pi.evalRingHom`. -/
def s2e_u1_analyticFunctionEvaluation (t : ℂ) :
    s2e_u1_analyticFunctionRing →+* ℂ :=
  (Pi.evalRingHom (fun _ : ℂ => ℂ) t).comp s2e_u1_analyticFunctionRing.subtype

/-- Divisibility of monic polynomial families near zero gives divisibility
in the actual analytic germ ring. Pointwise root multiplicities can therefore
be used without choosing differentiable ordered roots.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, divisor coefficient charts;
Mathlib, `Polynomial.map_modByMonic`. -/
theorem s2e_u1_analytic_polynomial_germ_dvd_of_eventually_dvd
    (P Q : Polynomial s2e_u1_analyticFunctionRing) (hP : P.Monic)
    (hdiv : ∀ᶠ t in 𝓝 (0 : ℂ),
      P.map (s2e_u1_analyticFunctionEvaluation t) ∣
        Q.map (s2e_u1_analyticFunctionEvaluation t)) :
    P.map s2e_u1_analyticFunctionGerm ∣ Q.map s2e_u1_analyticFunctionGerm := by
  have hm : (Q %ₘ P).map s2e_u1_analyticFunctionGerm = 0 := by
    apply Polynomial.ext
    intro n
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    apply Subtype.ext
    change ((fun t => ((Q %ₘ P).coeff n).val t) : Germ (𝓝 (0 : ℂ)) ℂ) =
      ((fun _ : ℂ => (0 : ℂ)) : Germ (𝓝 (0 : ℂ)) ℂ)
    apply Germ.coe_eq.mpr
    filter_upwards [hdiv] with t ht
    have he : (Q %ₘ P).map (s2e_u1_analyticFunctionEvaluation t) = 0 := by
      rw [Polynomial.map_modByMonic _ hP]
      exact (Polynomial.modByMonic_eq_zero_iff_dvd (hP.map _)).mpr ht
    have hh := congrArg (fun R : Polynomial ℂ => R.coeff n) he
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hh
    exact hh
  rw [Polynomial.map_modByMonic _ hP] at hm
  exact (Polynomial.modByMonic_eq_zero_iff_dvd (hP.map _)).mp hm

/-- Pointwise divisibility of analytic monic families supplies an actual
factorization of their dual-number coefficient jets, including at collisions.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, divisor coefficient charts;
Hartshorne, Algebraic Geometry, II.8, first-order jets. -/
theorem s2e_u1_analytic_polynomial_jet_factor_of_eventually_dvd
    (P Q : Polynomial s2e_u1_analyticFunctionRing) (hP : P.Monic)
    (hdiv : ∀ᶠ t in 𝓝 (0 : ℂ),
      P.map (s2e_u1_analyticFunctionEvaluation t) ∣
        Q.map (s2e_u1_analyticFunctionEvaluation t)) :
    ∃ R : Polynomial (DualNumber ℂ),
      Q.map (s2e_u1_analyticGermJet.comp s2e_u1_analyticFunctionGerm) =
        P.map (s2e_u1_analyticGermJet.comp s2e_u1_analyticFunctionGerm) * R := by
  obtain ⟨R, hR⟩ := s2e_u1_analytic_polynomial_germ_dvd_of_eventually_dvd P Q hP hdiv
  refine ⟨R.map s2e_u1_analyticGermJet, ?_⟩
  rw [← Polynomial.map_map, hR, Polynomial.map_mul, Polynomial.map_map]

/-- A monic analytic total polynomial gives a monic complementary jet factor.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, effective divisor factors;
Mathlib, `Polynomial.Monic.of_mul_monic_left`. -/
theorem s2e_u1_analytic_polynomial_jet_monic_factor_of_eventually_dvd
    (P Q : Polynomial s2e_u1_analyticFunctionRing) (hP : P.Monic) (hQ : Q.Monic)
    (hdiv : ∀ᶠ t in 𝓝 (0 : ℂ),
      P.map (s2e_u1_analyticFunctionEvaluation t) ∣
        Q.map (s2e_u1_analyticFunctionEvaluation t)) :
    ∃ R : Polynomial (DualNumber ℂ), R.Monic ∧
      Q.map (s2e_u1_analyticGermJet.comp s2e_u1_analyticFunctionGerm) =
        P.map (s2e_u1_analyticGermJet.comp s2e_u1_analyticFunctionGerm) * R := by
  obtain ⟨R, hR⟩ := s2e_u1_analytic_polynomial_jet_factor_of_eventually_dvd P Q hP hdiv
  refine ⟨R, ?_, hR⟩
  apply (hP.map _).of_mul_monic_left
  rw [← hR]
  exact hQ.map _

end HodgeLean.Foundations.Program
