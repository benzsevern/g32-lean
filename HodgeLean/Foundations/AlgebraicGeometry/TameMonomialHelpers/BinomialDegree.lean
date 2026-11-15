import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.FieldHelpers
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.Roots

/-! # Degree of a binomial with a primitive scalar action
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.TameMonomialCover.Helpers

/-- A nonzero primitive eigenvector has distinct iterates up to the root's period.
Source: Mathlib, IsPrimitiveRoot.pow_inj and IsPrimitiveRoot.map_of_injective. -/
theorem eigen_orbit_injective
    {F K : Type*} [CommRing F] [Field K] [Algebra F K]
    (hinj : Function.Injective (algebraMap F K))
    (m : ℕ) (ζ : F) (hζ : IsPrimitiveRoot ζ m)
    (d : K ≃ₐ[F] K) (v : K) (hv : v ≠ 0)
    (hd : d v = algebraMap F K ζ * v) :
    Function.Injective (fun i : Fin m => (d ^ i.val) v) := by
  have hζK : IsPrimitiveRoot (algebraMap F K ζ) m :=
    hζ.map_of_injective hinj
  intro i j hij
  apply Fin.ext
  apply hζK.pow_inj i.isLt j.isLt
  apply mul_right_cancel₀ hv
  simpa only [aut_pow_generator d v ζ hd] using hij

/-- Every nonzero polynomial annihilating a primitive eigenvector has degree at least its scalar period.
Source: Mathlib, Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero and Polynomial.aeval_algHom_apply. -/
theorem eigen_annihilator_degree
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K))
    (m : ℕ) (ζ : R) (hζ : IsPrimitiveRoot ζ m)
    (d : K ≃ₐ[R] K) (v : K) (hv : v ≠ 0)
    (hd : d v = algebraMap R K ζ * v)
    (P : Polynomial R) (hP : P ≠ 0) (hroot : Polynomial.aeval v P = 0) :
    m ≤ P.natDegree := by
  by_contra hdeg
  have horbit : ∀ i : Fin m,
      (P.map (algebraMap R K)).eval ((d ^ i.val) v) = 0 := by
    intro i
    rw [Polynomial.eval_map_algebraMap, Polynomial.aeval_algHom_apply, hroot, map_zero]
  have hlt : (P.map (algebraMap R K)).natDegree < Fintype.card (Fin m) := by
    simpa only [Fintype.card_fin] using
      lt_of_le_of_lt Polynomial.natDegree_map_le (Nat.lt_of_not_ge hdeg)
  have H := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (P.map (algebraMap R K))
    (eigen_orbit_injective hinj m ζ hζ d v hv hd) horbit hlt
  exact ((Polynomial.map_ne_zero_iff hinj).mpr hP) H

/-- A binomial admitting a nonzero primitive eigenvector is irreducible over its embedded coefficient domain.
Source: Mathlib, Polynomial.Monic.irreducible_iff_natDegree and Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero. -/
theorem binomial_irreducible
    {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K))
    (m : ℕ) (hm : 0 < m) (ζ : R) (hζ : IsPrimitiveRoot ζ m)
    (d : K ≃ₐ[R] K) (v : K) (hv : v ≠ 0)
    (hd : d v = algebraMap R K ζ * v)
    (q : R) (heq : v ^ m = algebraMap R K q) :
    Irreducible ((Polynomial.X : Polynomial R) ^ m - Polynomial.C q) := by
  have hmon := Polynomial.monic_X_pow_sub_C q hm.ne'
  apply hmon.irreducible_iff_natDegree.mpr
  constructor
  · intro H
    have Hdeg := congrArg Polynomial.natDegree H
    rw [Polynomial.natDegree_X_pow_sub_C, Polynomial.natDegree_one] at Hdeg
    exact hm.ne' Hdeg
  · intro P Q hP hQ hPQ
    have hsum : P.natDegree + Q.natDegree = m := by
      rw [← hP.natDegree_mul hQ, hPQ, Polynomial.natDegree_X_pow_sub_C]
    have hz : Polynomial.aeval v P * Polynomial.aeval v Q = 0 := by
      rw [← map_mul, hPQ]
      simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, heq, sub_self]
    rcases mul_eq_zero.mp hz with hz | hz
    · right
      have H := eigen_annihilator_degree hinj m ζ hζ d v hv hd P hP.ne_zero hz
      omega
    · left
      have H := eigen_annihilator_degree hinj m ζ hζ d v hv hd Q hQ.ne_zero hz
      omega

end AlgebraicGeometry.TameMonomialCover.Helpers
