import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal

/-! # Radical of the extended ideal at a singleton prime fiber -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A unique prime above a maximal ideal is the radical of its extension.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.14. -/
theorem s2e_singleton_prime_fiber_radical
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (m : Ideal R) [hm : m.IsMaximal] (P : Ideal S) [hP : P.IsPrime]
    (hPm : P.comap f = m)
    (huniq : ∀ Q : Ideal S, Q.IsPrime → Q.comap f = m → Q = P) :
    (m.map f).radical = P := by
  apply le_antisymm
  · apply hP.radical_le_iff.mpr
    rw [Ideal.map_le_iff_le_comap, hPm]
  · rw [Ideal.radical_eq_sInf]
    apply le_sInf
    intro Q hQ
    have hc : Q.comap f = m :=
      (hm.eq_of_le (Ideal.comap_ne_top f hQ.2.ne_top)
        (Ideal.le_comap_of_map_le hQ.1)).symm
    exact le_of_eq (huniq Q hQ.2 hc).symm

#print axioms s2e_singleton_prime_fiber_radical
end HodgeLean.Foundations.Program
