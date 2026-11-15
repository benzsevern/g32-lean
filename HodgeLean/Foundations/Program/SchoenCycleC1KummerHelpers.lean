import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Paired exponents in a local cyclic equation
These algebraic identities do not identify a normalization chart.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Polynomial
namespace HodgeLean.Foundations.Program

/-- Dividing the covering coordinate by the exceptional parameter removes
an exponent pair whose sum is the covering degree. -/
theorem s2e_c1_paired_equation_divide {K : Type*} [Field K]
    (x v z u : K) (a b m : ℕ) (hx : x ≠ 0) (hab : a + b = m)
    (hz : z ^ m = x ^ a * (x * v) ^ b * u) :
    (z / x) ^ m = v ^ b * u := by
  rw [div_pow, hz, mul_pow]
  have he : x ^ a * (x ^ b * v ^ b) * u = x ^ m * (v ^ b * u) := by
    rw [← hab, pow_add]
    ring
  rw [he]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ hx)

/-- A root of a unit Kummer equation has invertible derivative whenever
the degree is invertible in the coefficient ring. -/
theorem s2e_c1_kummer_derivative_isUnit {R A : Type*}
    [CommRing R] [CommRing A] [Algebra R A]
    (m : ℕ) (hm : m ≠ 0) (u : R) (hu : IsUnit u)
    (hdegree : IsUnit (m : R)) (z : A)
    (hz : z ^ m = algebraMap R A u) :
    IsUnit (aeval z (derivative (X ^ m - C u : R[X]))) := by
  have hzunit : IsUnit z := (isUnit_pow_iff hm).mp (hz ▸ hu.map (algebraMap R A))
  simpa only [derivative_sub, derivative_X_pow, derivative_C, sub_zero,
    map_mul, aeval_C, map_pow, aeval_X] using
    (hdegree.map (algebraMap R A)).mul (hzunit.pow (m - 1))

/-- Inverting a derivative that is already a unit leaves the root algebra
unchanged and supplies its etale structure. -/
theorem s2e_c1_adjoinRoot_etale {R : Type*} [CommRing R]
    (f : R[X]) (hf : f.Monic) (hd : IsUnit (AdjoinRoot.mk f (derivative f))) :
    Algebra.Etale R (AdjoinRoot f) := by
  let P : StandardEtalePair R :=
    { f := f, monic_f := hf, g := derivative f,
      cond := ⟨1, 0, 1, by rw [mul_one, mul_zero, add_zero, pow_one]⟩ }
  let e := (IsLocalization.atUnit (AdjoinRoot f)
    (Localization.Away (AdjoinRoot.mk f (derivative f))) _ hd).restrictScalars R
  exact Algebra.Etale.of_equiv (P.equivAwayAdjoinRoot.trans e.symm)

/-- A Kummer root algebra over a unit has an etale structure when its degree
is invertible. -/
theorem s2e_c1_kummer_adjoinRoot_etale {R : Type*} [CommRing R]
    (m : ℕ) (hm : m ≠ 0) (u : R) (hu : IsUnit u)
    (hdegree : IsUnit (m : R)) :
    Algebra.Etale R (AdjoinRoot (X ^ m - C u : R[X])) := by
  apply s2e_c1_adjoinRoot_etale
  · exact monic_X_pow_sub_C u hm
  · rw [← AdjoinRoot.aeval_eq]
    apply s2e_c1_kummer_derivative_isUnit m hm u hu hdegree
    have h := AdjoinRoot.eval₂_root (X ^ m - C u : R[X])
    simpa only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero, AdjoinRoot.algebraMap_eq] using h

end HodgeLean.Foundations.Program
