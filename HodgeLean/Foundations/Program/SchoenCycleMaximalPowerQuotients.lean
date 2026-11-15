import HodgeLean.Foundations.Program.SchoenCycleLocalPowerMaps
import Mathlib.RingTheory.LocalRing.Quotient

/-! # Actual finite maximal-ideal neighbourhoods as local test algebras -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Every positive-order maximal-ideal neighbourhood of a local ring is local.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 3 and 10. -/
theorem s2e_maximal_power_quotient_isLocalRing
    (R : Type*) [CommRing R] [IsLocalRing R] (N : ℕ) (hN : 0 < N) :
    IsLocalRing (R ⧸ IsLocalRing.maximalIdeal R ^ N) := by
  have hm : IsLocalRing.maximalIdeal R ^ N ≤ IsLocalRing.maximalIdeal R :=
    Ideal.pow_le_self (Nat.ne_of_gt hN)
  have hI : IsLocalRing.maximalIdeal R ^ N ≠ ⊤ := by
    intro h
    rw [h] at hm
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp hm)
  letI : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ N) := Ideal.Quotient.nontrivial_iff.mpr hI
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N))
    Ideal.Quotient.mk_surjective

/-- The maximal ideal of the actual finite neighbourhood has the specified
nilpotence bound.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_maximal_power_quotient_maximalIdeal_pow
    (R : Type*) [CommRing R] [IsLocalRing R] (N : ℕ) (hN : 0 < N) :
    letI := s2e_maximal_power_quotient_isLocalRing R N hN
    IsLocalRing.maximalIdeal (R ⧸ IsLocalRing.maximalIdeal R ^ N) ^ N = ⊥ := by
  letI := s2e_maximal_power_quotient_isLocalRing R N hN
  have he := IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N)) Ideal.Quotient.mk_surjective
  rw [← he, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]

end HodgeLean.Foundations.Program
