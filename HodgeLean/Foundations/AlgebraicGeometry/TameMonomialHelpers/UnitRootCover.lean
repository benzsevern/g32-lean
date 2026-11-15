import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.CoordinateRootCover
import Mathlib.RingTheory.Etale.StandardEtale

/-! # The etale unit-root part of a monomial cover
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Polynomial
namespace AlgebraicGeometry.TameMonomialCover.Helpers

/-- The standard etale presentation for a positive-degree coefficient root, with the root inverted.
Source: Mathlib, StandardEtalePair and Polynomial.derivative_X_pow. -/
def unitRootPair
    (R : Type*) [CommRing R] (m : ℕ) (hm : 0 < m) (ε a : R)
    (ha : (m : R) * a = 1) : StandardEtalePair R where
  f := X ^ m - C ε
  monic_f := monic_X_pow_sub_C ε hm.ne'
  g := X
  cond := by
    refine ⟨C a, 0, m - 1, ?_⟩
    rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero, mul_zero, add_zero]
    rw [mul_right_comm, ← C_mul, ha, C_1, one_mul]

example (R : Type*) [CommRing R] (m : ℕ) (hm : 0 < m) (ε a : R)
    (ha : (m : R) * a = 1) :
    (unitRootPair R m hm ε a ha).f = X ^ m - C ε := rfl

/-- When the coefficient is a unit, the standard etale unit-root cover is an integral extension of the base.
Source: Mathlib, AdjoinRoot.isIntegral_of_monic, IsLocalization.atUnit and StandardEtalePair.equivAwayAdjoinRoot. -/
theorem unitRootPair_integral
    (R : Type*) [CommRing R] (m : ℕ) (hm : 0 < m) (ε a : R)
    (ha : (m : R) * a = 1) (hε : IsUnit ε) :
    Algebra.IsIntegral R (unitRootPair R m hm ε a ha).Ring := by
  let f : R[X] := X ^ m - C ε
  let P := unitRootPair R m hm ε a ha
  have hroot : AdjoinRoot.root f ^ m = algebraMap R (AdjoinRoot f) ε := by
    have H : aeval (AdjoinRoot.root f) f = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    simpa only [f, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using H
  have hunit : IsUnit (AdjoinRoot.root f) := (isUnit_pow_iff hm.ne').mp (by
    rw [hroot]
    exact hε.map (algebraMap R (AdjoinRoot f)))
  let S := Localization.Away (AdjoinRoot.root f)
  let e : P.Ring ≃ₐ[R] AdjoinRoot f := P.equivAwayAdjoinRoot.trans
    (((IsLocalization.atUnit (AdjoinRoot f) (S := S) (AdjoinRoot.root f) hunit).symm).restrictScalars R)
  letI : Algebra.IsIntegral R (AdjoinRoot f) :=
    AdjoinRoot.isIntegral_of_monic (monic_X_pow_sub_C ε hm.ne')
  exact (AlgEquiv.isIntegral_iff e).mpr inferInstance

/-- A compatible invertible coefficient root gives a map from the standard etale unit-root cover with the prescribed base and root values.
Source: Mathlib, StandardEtalePair.lift, StandardEtalePair.lift_X and AlgHom.commutes. -/
theorem unitRootPair_lift
    {R L : Type*} [CommRing R] [CommRing L]
    (m : ℕ) (hm : 0 < m) (ε a : R) (ha : (m : R) * a = 1)
    (f : R →+* L) (u : L) (hu : u ^ m = f ε) (hunit : IsUnit u) :
    ∃ τ : (unitRootPair R m hm ε a ha).Ring →+* L,
      (∀ r, τ (algebraMap R _ r) = f r) ∧
      τ (unitRootPair R m hm ε a ha).X = u := by
  let P := unitRootPair R m hm ε a ha
  letI := f.toAlgebra
  have H : P.HasMap u := by
    constructor
    · change aeval u (X ^ m - C ε) = 0
      rw [map_sub, map_pow, aeval_X, aeval_C]
      change u ^ m - f ε = 0
      rw [hu, sub_self]
    · change IsUnit (aeval u X)
      rw [aeval_X]
      exact hunit
  exact ⟨(P.lift u H).toRingHom, (P.lift u H).commutes, P.lift_X u H⟩

end AlgebraicGeometry.TameMonomialCover.Helpers
