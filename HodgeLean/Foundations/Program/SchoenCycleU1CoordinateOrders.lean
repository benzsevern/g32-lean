import HodgeLean.Foundations.Program.SchoenCycleDivisorEnumeration
import HodgeLean.Foundations.AnalyticDivisorAlgebraic4
import Mathlib.Algebra.Polynomial.Roots

/-! # Orders of retained coordinate divisor polynomials -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The coordinate polynomial counts the entire coordinate fibre, including
all repeated entries of the actual point tuple.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, effective divisors;
Mathlib, `Polynomial.roots_multiset_prod_X_sub_C`. -/
theorem s2e_u1_coordinate_polynomial_rootMultiplicity
    {C : Type*} {N : ℕ} (x : Fin N → C) (c : C → ℂ) (a : ℂ) :
    (∏ i : Fin N, (Polynomial.X - Polynomial.C (c (x i)))).rootMultiplicity a =
      Fintype.card {i : Fin N // c (x i) = a} := by
  classical
  have hr : (∏ i : Fin N, (Polynomial.X - Polynomial.C (c (x i)))).roots =
      (List.ofFn (fun i => c (x i)) : Multiset ℂ) := by
    have h := Polynomial.roots_multiset_prod_X_sub_C
      (List.ofFn (fun i => c (x i)) : Multiset ℂ)
    simpa only [Multiset.map_coe, List.map_ofFn, Multiset.prod_coe,
      List.prod_ofFn, Function.comp_apply] using h
  rw [← Polynomial.count_roots, hr, Multiset.coe_count]
  exact s2e_tuple_count_eq_fiber_card _ _

/-- In a regular analytic coordinate, the order of the evaluated retained
polynomial is exactly the multiplicity of its full coordinate fibre.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I;
Mathlib, `analyticOrderAt_comp_of_deriv_ne_zero`. -/
theorem s2e_u1_coordinate_polynomial_analyticOrder
    {C : Type*} {N : ℕ} (x : Fin N → C) (c : C → ℂ)
    (g : ℂ → ℂ) (z : ℂ) (hg : AnalyticAt ℂ g z) (hg' : deriv g z ≠ 0) :
    analyticOrderAt (fun w =>
      (∏ i : Fin N, (Polynomial.X - Polynomial.C (c (x i)))).eval (g w)) z =
        (Fintype.card {i : Fin N // c (x i) = g z} : ℕ∞) := by
  let P := ∏ i : Fin N, (Polynomial.X - Polynomial.C (c (x i)))
  have hP : P ≠ 0 := (Polynomial.monic_prod_X_sub_C (fun i => c (x i)) Finset.univ).ne_zero
  change analyticOrderAt ((fun w => P.eval w) ∘ g) z = _
  rw [analyticOrderAt_comp_of_deriv_ne_zero hg hg',
    HodgeLean.Foundations.AnalyticDivisorAlgebraic4.spec_analyticOrderAt_polynomial_eval hP,
    s2e_u1_coordinate_polynomial_rootMultiplicity]

/-- The evaluated coordinate polynomial has order at least the multiplicity
of any point in the divisor tuple, even if the coordinate identifies other points.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, multiplicities of effective divisors. -/
theorem s2e_u1_coordinate_polynomial_analyticOrder_lower_bound
    {C : Type*} [DecidableEq C] {N : ℕ} (x : Fin N → C) (c : C → ℂ)
    (g : ℂ → ℂ) (z : ℂ) (hg : AnalyticAt ℂ g z) (hg' : deriv g z ≠ 0)
    (p : C) (hp : g z = c p) :
    (Fintype.card {i : Fin N // x i = p} : ℕ∞) ≤
      analyticOrderAt (fun w =>
        (∏ i : Fin N, (Polynomial.X - Polynomial.C (c (x i)))).eval (g w)) z := by
  classical
  rw [s2e_u1_coordinate_polynomial_analyticOrder x c g z hg hg']
  have hle : Fintype.card {i : Fin N // x i = p} ≤
      Fintype.card {i : Fin N // c (x i) = g z} := by
    apply Fintype.card_le_of_injective
      (fun i : {i : Fin N // x i = p} => (⟨i.val, by rw [i.property, hp]⟩ : {i : Fin N // c (x i) = g z}))
    intro i j h
    apply Subtype.ext
    exact congrArg (fun q : {i : Fin N // c (x i) = g z} => q.val) h
  exact_mod_cast hle

/-- When the chosen coordinate separates a specified support point, the
numerator order equals its exact point multiplicity, with repetitions retained.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, divisor coordinates. -/
theorem s2e_u1_coordinate_polynomial_analyticOrder_of_separation
    {C : Type*} [DecidableEq C] {N : ℕ} (x : Fin N → C) (c : C → ℂ)
    (g : ℂ → ℂ) (z : ℂ) (hg : AnalyticAt ℂ g z) (hg' : deriv g z ≠ 0)
    (p : C) (hsep : ∀ i, c (x i) = g z ↔ x i = p) :
    analyticOrderAt (fun w =>
      (∏ i : Fin N, (Polynomial.X - Polynomial.C (c (x i)))).eval (g w)) z =
        (Fintype.card {i : Fin N // x i = p} : ℕ∞) := by
  rw [s2e_u1_coordinate_polynomial_analyticOrder x c g z hg hg']
  congr 1
  exact Fintype.card_congr (Equiv.subtypeEquivRight hsep)

end HodgeLean.Foundations.Program
