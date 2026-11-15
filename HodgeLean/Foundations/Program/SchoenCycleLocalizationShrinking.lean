import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Finiteness.Basic

/-! # Finite ideal comparisons on localization neighborhoods -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A containment of localized finitely generated ideals has one common
denominator witnessing containment before localization.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 3,
Propositions 3.3 and 3.8. -/
theorem s2e_finite_ideal_localized_containment_denominator
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (I J : Ideal R) (hI : I.FG)
    (h : I.map (algebraMap R S) ≤ J.map (algebraMap R S)) :
    ∃ s ∈ M, ∀ x ∈ I, s * x ∈ J := by
  classical
  obtain ⟨b, hb⟩ := hI
  have hx (i : b) : ∃ t ∈ M, t * (i : R) ∈ J := by
    apply (IsLocalization.algebraMap_mem_map_algebraMap_iff M S J i).mp
    apply h
    apply Ideal.mem_map_of_mem
    rw [← hb]
    exact Ideal.subset_span i.property
  choose t ht hj using hx
  let s : R := ∏ i : b, t i
  refine ⟨s, M.prod_mem (fun i _ => ht i), ?_⟩
  have hle : I ≤ Submodule.comap (LinearMap.mul R R s) J := by
    rw [← hb]
    apply Submodule.span_le.mpr
    intro x hx
    let i : b := ⟨x, hx⟩
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun i : b => t i) (Finset.mem_univ i)
    change s * x ∈ J
    change s = t i * r at hr
    rw [hr]
    have he : t i * r * x = r * (t i * x) := by ring
    rw [he]
    exact J.mul_mem_left r (hj i)
  intro x hx
  exact hle hx

#print axioms s2e_finite_ideal_localized_containment_denominator
/-- A denominator witnessing ideal containment gives containment after any
ring map making that denominator a unit.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 3. -/
theorem s2e_ideal_map_le_of_unit_denominator
    {R T : Type*} [CommRing R] [CommRing T] (I J : Ideal R) (s : R)
    (hs : ∀ x ∈ I, s * x ∈ J) (f : R →+* T) (hu : IsUnit (f s)) :
    I.map f ≤ J.map f := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  apply (Ideal.unit_mul_mem_iff_mem (J.map f) hu).mp
  rw [← map_mul]
  exact Ideal.mem_map_of_mem f (hs x hx)

#print axioms s2e_ideal_map_le_of_unit_denominator
/-- Equality of two finite ideals at a localization persists after inverting
one denominator, for every target ring.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 3,
Propositions 3.3 and 3.8. -/
theorem s2e_finite_ideals_localized_equality_denominator
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (I J : Ideal R) (hI : I.FG) (hJ : J.FG)
    (h : I.map (algebraMap R S) = J.map (algebraMap R S)) :
    ∃ s ∈ M, ∀ {T : Type*} [CommRing T] (f : R →+* T),
      IsUnit (f s) → I.map f = J.map f := by
  obtain ⟨s, hs, hst⟩ := s2e_finite_ideal_localized_containment_denominator M I J hI h.le
  obtain ⟨t, ht, hts⟩ := s2e_finite_ideal_localized_containment_denominator M J I hJ h.symm.le
  refine ⟨s * t, M.mul_mem hs ht, ?_⟩
  intro T _ f hu
  rw [map_mul, IsUnit.mul_iff] at hu
  exact le_antisymm (s2e_ideal_map_le_of_unit_denominator I J s hst f hu.1)
    (s2e_ideal_map_le_of_unit_denominator J I t hts f hu.2)

#print axioms s2e_finite_ideals_localized_equality_denominator
end HodgeLean.Foundations.Program
