module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Tactic

/-! # Independent infinitesimal coefficient check
A monic quadratic retains a nonzero first-order coefficient variation at a double root.
HC no distance; AV milestone no distance.
-/
public section

namespace HodgeLean.Foundations.Program

/-- A first-order perturbation of a double-root polynomial is visible in its coefficients.
Source: ACGH, Geometry of Algebraic Curves I, Chapter IV, infinitesimal divisors. -/
theorem s2e_s1b_check_collision_variation :
    (Polynomial.X ^ 2 - Polynomial.C (DualNumber.eps : DualNumber ℂ)) ≠
      Polynomial.X ^ 2 := by
  intro h
  have hc := congrArg (fun p : Polynomial (DualNumber ℂ) => p.coeff 0) h
  have he : (DualNumber.eps : DualNumber ℂ) ≠ 0 := by
    intro hz
    have hs := congrArg TrivSqZeroExt.snd hz
    exact one_ne_zero (show (1 : ℂ) = 0 from hs)
  exact he (by simpa using hc)

#print axioms s2e_s1b_check_collision_variation
end HodgeLean.Foundations.Program
