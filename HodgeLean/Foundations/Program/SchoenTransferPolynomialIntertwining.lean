import Mathlib.LinearAlgebra.Eigenspace.Minpoly

namespace HodgeLean.Foundations.Program

/-- A linear intertwiner transports polynomial evaluations over the coefficient field. -/
theorem s4_polynomial_intertwines {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (L : V →ₗ[K] W) (A : Module.End K V) (B : Module.End K W)
    (h : ∀ x, L (A x) = B (L x)) (P : Polynomial K) (x : V) :
    L (Polynomial.aeval A P x) = Polynomial.aeval B P (L x) := by
  have hp (n : ℕ) (y : V) : L ((A ^ n) y) = (B ^ n) (L y) := by
    induction n with
    | zero => simp only [pow_zero, Module.End.one_apply]
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, h, ih, pow_succ', Module.End.mul_apply]
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, LinearMap.add_apply, hP, hQ]
  | monomial n a =>
      simp only [Polynomial.aeval_monomial, Module.End.mul_apply,
        Module.algebraMap_end_apply, map_smul, hp]

end HodgeLean.Foundations.Program
