import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.BinomialDegree
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.MvPolynomial.Basic

/-! # Etale monomial parameter calculations
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.TameMonomialCover.Helpers

/-- An etale parameter algebra over a polynomial domain has an injective coefficient map when it is nontrivial.
Source: Mathlib, RingHom.Etale.toAlgebra, Module.Flat.isTorsionFree and FaithfulSMul.algebraMap_injective. -/
theorem etale_parameter_injective
    {k R : Type*} [Field k] [CommRing R] [Nontrivial R] [Algebra k R]
    (n : ℕ) (c : MvPolynomial (Fin n) k →ₐ[k] R) (hc : c.toRingHom.Etale) :
    Function.Injective c := by
  letI := c.toRingHom.toAlgebra
  letI : Algebra.Etale (MvPolynomial (Fin n) k) R := hc.toAlgebra
  exact FaithfulSMul.algebraMap_injective (MvPolynomial (Fin n) k) R

/-- Every coordinate monomial times a unit is nonzero in an etale parameter domain.
Source: Mathlib, MvPolynomial.X_ne_zero, IsUnit.ne_zero and Finset.prod_ne_zero_iff. -/
theorem etale_monomial_ne_zero
    {k R : Type*} [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    (n : ℕ) (c : MvPolynomial (Fin n) k →ₐ[k] R) (hc : c.toRingHom.Etale)
    (α : Fin n → ℕ) (ε : R) (hε : IsUnit ε) :
    ε * ∏ i, (c (MvPolynomial.X i)) ^ α i ≠ 0 := by
  have hinj := etale_parameter_injective n c hc
  have hX (i : Fin n) : c (MvPolynomial.X i) ≠ 0 := by
    intro H
    apply MvPolynomial.X_ne_zero (R := k) i
    apply hinj
    rw [H, map_zero]
  exact mul_ne_zero hε.ne_zero
    (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hX i))

/-- A generator of the stated etale monomial field equation is nonzero.
Source: Mathlib, map_ne_zero_iff and pow_ne_zero; etale parameter injectivity. -/
theorem etale_monomial_generator_ne_zero
    {k R K : Type*} [Field k] [CommRing R] [IsDomain R] [Field K]
    [Algebra k R] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K))
    (n m : ℕ) (hm : 0 < m)
    (c : MvPolynomial (Fin n) k →ₐ[k] R) (hc : c.toRingHom.Etale)
    (α : Fin n → ℕ) (ε : R) (hε : IsUnit ε) (v : K)
    (hv : v ^ m = algebraMap R K ε *
      ∏ i, (algebraMap R K (c (MvPolynomial.X i))) ^ α i) : v ≠ 0 := by
  have hq := etale_monomial_ne_zero n c hc α ε hε
  have heq : v ^ m = algebraMap R K (ε * ∏ i, (c (MvPolynomial.X i)) ^ α i) := by
    simpa only [map_mul, map_prod, map_pow] using hv
  intro hz
  have H : algebraMap R K (ε * ∏ i, (c (MvPolynomial.X i)) ^ α i) = 0 := by
    rw [← heq, hz, zero_pow hm.ne']
  apply hq
  apply hinj
  rw [H, map_zero]

end AlgebraicGeometry.TameMonomialCover.Helpers
