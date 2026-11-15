import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Nilpotent.Lemmas

/-! # Local maps to finite infinitesimal test algebras -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A local map to an algebra with vanishing maximal-ideal power kills the
same maximal-ideal power in its source.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 3,
local homomorphisms and ideal powers. -/
theorem s2e_local_map_maximal_power_kernel
    (R A : Type*) [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A]
    (f : R →+* A) [IsLocalHom f] (N : ℕ)
    (hA : IsLocalRing.maximalIdeal A ^ N = ⊥) :
    IsLocalRing.maximalIdeal R ^ N ≤ RingHom.ker f := by
  have hm : (IsLocalRing.maximalIdeal R ^ N).map f ≤ IsLocalRing.maximalIdeal A ^ N := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' (IsLocalRing.map_maximalIdeal_le f) N
  intro r hr
  have h := hm (Ideal.mem_map_of_mem f hr)
  rw [hA] at h
  exact h

/-- A local algebra map into a test algebra with vanishing maximal-ideal
power descends to the matching finite neighbourhood of its source.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 3 and 10. -/
def s2e_local_power_quotient_lift
    (K R A : Type*) [CommSemiring K] [CommRing R] [IsLocalRing R] [Algebra K R]
    [CommRing A] [IsLocalRing A] [Algebra K A]
    (f : R →ₐ[K] A) [IsLocalHom f.toRingHom] (N : ℕ)
    (hA : IsLocalRing.maximalIdeal A ^ N = ⊥) :
    (R ⧸ IsLocalRing.maximalIdeal R ^ N) →ₐ[K] A :=
  Ideal.Quotient.liftₐ (IsLocalRing.maximalIdeal R ^ N) f
    (fun r hr => s2e_local_map_maximal_power_kernel R A f.toRingHom N hA hr)

/-- The descended finite-neighbourhood map evaluates every represented element
by the original local algebra map.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 3. -/
theorem s2e_local_power_quotient_lift_mk
    (K R A : Type*) [CommSemiring K] [CommRing R] [IsLocalRing R] [Algebra K R]
    [CommRing A] [IsLocalRing A] [Algebra K A]
    (f : R →ₐ[K] A) [IsLocalHom f.toRingHom] (N : ℕ)
    (hA : IsLocalRing.maximalIdeal A ^ N = ⊥) (r : R) :
    s2e_local_power_quotient_lift K R A f N hA
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N) r) = f r := rfl

/-- Every ring map from a local algebra with nilpotent maximal ideal to
another local ring is local.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 1 and 8. -/
theorem s2e_nilpotent_maximal_source_map_local
    (R A : Type*) [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A]
    (f : R →+* A) (N : ℕ) (hR : IsLocalRing.maximalIdeal R ^ N = ⊥) : IsLocalHom f := by
  apply ((IsLocalRing.local_hom_TFAE f).out 4 1).mp
  intro r hr
  have hn : r ^ N = 0 := by
    have h := Ideal.pow_mem_pow hr N
    rw [hR] at h
    exact h
  have hf : IsNilpotent (f r) := ⟨N, by rw [← map_pow, hn, map_zero]⟩
  exact nilpotent_iff_mem_prime.mp hf (IsLocalRing.maximalIdeal A) inferInstance

end HodgeLean.Foundations.Program
