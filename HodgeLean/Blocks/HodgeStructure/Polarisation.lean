import HodgeLean.Blocks.HodgeStructure.Basic
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! # Polarisations of pure rational Hodge structures

This is the rational version of Cattani--El Zein--Griffiths--Lê, *Hodge Theory*,
pre-publication version (20 October 2013), Chapter 3, Definition 3.1.8.
-/

open scoped TensorProduct
noncomputable section

namespace HodgeBlocks

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-- The integral power of `i` occurring in the Hodge--Riemann Hermitian form.
Using `zpow` makes negative Hodge indices meaningful; powers of `i` are automatically
periodic modulo four. -/
def Iexp (m : ℤ) : ℂ := Complex.I ^ m

@[simp] theorem Iexp_zero : Iexp 0 = 1 := by simp [Iexp]

/-- A polarisation of a pure rational Hodge structure.

The form is first defined over `ℚ`; `form.baseChange ℂ` is its complex-bilinear extension.
Thus an `x ∈ M.H (p,q)` already lies in `ℂ ⊗[ℚ] V`, and rational conjugation
`sigmaQ V x` can be used directly in the positivity conditions.
-/
structure Polarisation {n : ℤ} (M : QHodgeStructure n V) where
  form : LinearMap.BilinForm ℚ V
  nondegenerate : form.Nondegenerate
  symm : ∀ x y, form x y = ((-1 : ℚ) ^ n) * form y x
  orthogonal : ∀ p q p' q' : ℤ, (p', q') ≠ (q, p) →
    ∀ x ∈ M.H (p, q), ∀ y ∈ M.H (p', q'), form.baseChange ℂ x y = 0
  hermitian_real : ∀ p q : ℤ, p + q = n → ∀ x ∈ M.H (p, q),
    (Iexp (p - q) * form.baseChange ℂ x (sigmaQ V x)).im = 0
  positive : ∀ p q : ℤ, p + q = n → ∀ x ∈ M.H (p, q), x ≠ 0 →
    0 < (Iexp (p - q) * form.baseChange ℂ x (sigmaQ V x)).re

namespace Polarisation

variable {n : ℤ} {M : QHodgeStructure n V}

/-- The parity symmetry condition, exposed as a convenient projection lemma. -/
theorem form_swap (P : Polarisation M) (x y : V) :
    P.form x y = ((-1 : ℚ) ^ n) * P.form y x :=
  P.symm x y

/-- Distinct non-conjugate Hodge bidegrees are orthogonal after complexification. -/
theorem orthogonal_of_ne_swap (P : Polarisation M) {p q p' q' : ℤ}
    (h : (p', q') ≠ (q, p)) {x y : ℂ ⊗[ℚ] V}
    (hx : x ∈ M.H (p, q)) (hy : y ∈ M.H (p', q')) :
    P.form.baseChange ℂ x y = 0 :=
  P.orthogonal p q p' q' h x hx y hy

end Polarisation

#print axioms Iexp
#print axioms Iexp_zero
#print axioms Polarisation
#print axioms Polarisation.form_swap
#print axioms Polarisation.orthogonal_of_ne_swap

end HodgeBlocks
