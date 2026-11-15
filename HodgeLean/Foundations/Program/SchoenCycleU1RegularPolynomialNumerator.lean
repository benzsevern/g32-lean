import HodgeLean.Foundations.Program.SchoenCycleU1DivisorJets

/-! # Actual regular polynomial numerators along parameter curves -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Evaluate an actual polynomial of regular sections along a parameter curve
and a curve coordinate. The finite coefficient formula is defined everywhere.
Source: Hartshorne, Algebraic Geometry, II.2, evaluation of regular sections. -/
def s2e_u1_regularPolynomialNumerator
    (X : Over (Spec ↧ℂ)) (U : X.left.Opens) (Q : Polynomial Γ(X.left, U))
    (c : ℂ → ComplexPoint X) (g : ℂ → ℂ) (tz : ℂ × ℂ) : ℂ :=
  ∑ j ∈ Q.support, Point.evaluate U (Q.coeff j) (c tz.1) * (g tz.2) ^ j

/-- Wherever the parameter curve lies in the chart, the numerator is exactly
the actual regular-section polynomial evaluated at that point.
Source: Hartshorne, Algebraic Geometry, II.2; Mathlib, `Polynomial.eval₂_eq_sum`. -/
theorem s2e_u1_regularPolynomialNumerator_evaluation
    (X : Over (Spec ↧ℂ)) (U : X.left.Opens) (Q : Polynomial Γ(X.left, U))
    (c : ℂ → ComplexPoint X) (g : ℂ → ℂ) (t z : ℂ)
    (ht : (c t).underlying ∈ U) :
    letI := s2e_step1_sectionAlgebra X U
    s2e_u1_regularPolynomialNumerator X U Q c g (t, z) =
      (Q.map (s2e_step1_pointEvaluation X U (c t)
        (s2e_step1_point_preimage X (c t) U ht)).toRingHom).eval (g z) := by
  letI := s2e_step1_sectionAlgebra X U
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  unfold s2e_u1_regularPolynomialNumerator
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun a : ℂ => a * (g z) ^ j)
    (s2e_u1_pointEvaluation_eq_evaluate X U (c t) ht (Q.coeff j)).symm

/-- Analytic section evaluations make the actual numerator jointly analytic
in the parameter and regular curve coordinate.
Source: Hartshorne, Algebraic Geometry, II.2; Serre, GAGA, section 2. -/
theorem s2e_u1_regularPolynomialNumerator_analyticAt
    (X : Over (Spec ↧ℂ)) (U : X.left.Opens) (Q : Polynomial Γ(X.left, U))
    (c : ℂ → ComplexPoint X) (g : ℂ → ℂ)
    (hc : ∀ s : Γ(X.left, U), AnalyticAt ℂ (fun t => Point.evaluate U s (c t)) 0)
    (hg : AnalyticAt ℂ g 0) :
    AnalyticAt ℂ (s2e_u1_regularPolynomialNumerator X U Q c g) (0, 0) := by
  unfold s2e_u1_regularPolynomialNumerator
  apply Finset.analyticAt_fun_sum
  intro j _
  exact ((hc _).comp_of_eq analyticAt_fst rfl).mul
    ((hg.comp_of_eq analyticAt_snd rfl).pow j)

/-- A stationary actual scheme-valued curve jet makes its regular-section
polynomial numerator stationary at every curve coordinate, including collisions.
Source: Hartshorne, Algebraic Geometry, II.8, tangent vectors and regular sections. -/
theorem s2e_u1_regularPolynomialNumerator_stationary
    (X : Over (Spec ↧ℂ)) (U : X.left.Opens) (hUa : IsAffineOpen U)
    (Q : Polynomial Γ(X.left, U)) (c : ℂ → ComplexPoint X) (g : ℂ → ℂ)
    (hU : ∀ᶠ t in 𝓝 (0 : ℂ), (c t).underlying ∈ U)
    (hc : ∀ s : Γ(X.left, U), AnalyticAt ℂ (fun t => Point.evaluate U s (c t)) 0)
    (h0 : (c 0).underlying ∈ U)
    (he : s2e_u1_curveJet X U hUa c hU hc =
      s2e_u1_curveJet X U hUa (fun _ => c 0)
        (Filter.Eventually.of_forall (fun _ => h0)) (fun _ => analyticAt_const)) :
    ∀ z : ℂ, deriv (fun t => s2e_u1_regularPolynomialNumerator X U Q c g (t, z)) 0 = 0 := by
  intro z
  have hd (j : ℕ) : deriv (fun t => Point.evaluate U (Q.coeff j) (c t)) 0 = 0 :=
    s2e_u1_curveJet_stationary_coefficients X U hUa c hU hc h0 he Q j
  have hs := HasDerivAt.fun_sum (u := Q.support)
    (fun j _ => (hc (Q.coeff j)).differentiableAt.hasDerivAt.mul_const ((g z) ^ j))
  simpa only [s2e_u1_regularPolynomialNumerator, hd, zero_mul, Finset.sum_const_zero] using hs.deriv

end HodgeLean.Foundations.Program
