import HodgeLean.Foundations.Program.SchoenTowerT11bIrreducibleCurves
import Mathlib.RingTheory.Radical.Basic

/-! Removing repeated factors while retaining specialized zero sets.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open UniqueFactorizationMonoid

/-- Removing factor multiplicities preserves vanishing under any map to a domain.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, polynomial factorization step. -/
theorem s2v_t11b_radical_map_zero_iff {R S : Type*}
    [CommRing R] [IsDomain R] [NormalizationMonoid R] [UniqueFactorizationMonoid R]
    [CommRing S] [IsDomain S] (φ : R →+* S) (a : R) (ha : a ≠ 0) :
    φ (radical a) = 0 ↔ φ a = 0 := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := (radical_dvd_self : radical a ∣ a)
    rw [hb, map_mul, h, zero_mul]
  · intro h
    obtain ⟨n, b, hb⟩ := exists_dvd_radical_self_pow ha
    apply eq_zero_of_pow_eq_zero (n := n)
    rw [← map_pow, hb, map_mul, h, zero_mul]

/-- Removing repeated factors preserves every real fiber of a nonzero plane equation.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, polynomial factorization step. -/
theorem s2v_t11b_radical_family_zero_iff
    (P : Polynomial (Polynomial ℝ)) (hP : P ≠ 0) (t x : ℝ) :
    (radical P).eval₂ (Polynomial.evalRingHom t) x = 0 ↔
      P.eval₂ (Polynomial.evalRingHom t) x = 0 := by
  exact s2v_t11b_radical_map_zero_iff
    (Polynomial.eval₂RingHom (Polynomial.evalRingHom t) x) P hP

end HodgeLean.Foundations.Program
