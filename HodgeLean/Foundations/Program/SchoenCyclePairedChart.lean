import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # The paired Cartier calculation in a blowup chart
A paired restriction cancels the regular exceptional parameter on the slice.
-/

namespace HodgeLean.Foundations.Program

/-- If paired ideals generate a principal centre and have equal images on a
Cartier slice, the first ideal contains a multiple of the centre generator
whose residual factor restricts to one. -/
theorem s2e_paired_chart_unit_factor
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ) (I J : Ideal R) (z : R)
    (hcentre : I ⊔ J = Ideal.span {z})
    (hpair : Ideal.map φ I = Ideal.map φ J)
    (hregular : Function.Injective (fun a : S => a * φ z)) :
    ∃ a : R, φ a = 1 ∧ a * z ∈ I := by
  have hz : z ∈ I ⊔ J := by
    rw [hcentre]
    exact Ideal.subset_span (Set.mem_singleton z)
  have hzmap : φ z ∈ Ideal.map φ I := by
    have h := Ideal.mem_map_of_mem φ hz
    rw [Ideal.map_sup, ← hpair, sup_idem] at h
    exact h
  obtain ⟨i, hi, hφi⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).mp hzmap
  have hispan : i ∈ Ideal.span {z} := by
    rw [← hcentre]
    exact (le_sup_left : I ≤ I ⊔ J) hi
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hispan
  refine ⟨a, ?_, ?_⟩
  · apply hregular
    change φ a * φ z = 1 * φ z
    rw [← map_mul, ha, hφi, one_mul]
  · rwa [ha]

/-- Dividing a branch ideal by the exceptional parameter gives the unit
ideal after restriction to the paired Cartier slice. -/
theorem s2e_paired_chart_colon_map_top
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ) (I J : Ideal R) (z : R)
    (hcentre : I ⊔ J = Ideal.span {z})
    (hpair : Ideal.map φ I = Ideal.map φ J)
    (hregular : Function.Injective (fun a : S => a * φ z)) :
    Ideal.map φ (I.colon (Ideal.span {z})) = ⊤ := by
  obtain ⟨a, ha, haz⟩ := s2e_paired_chart_unit_factor φ hφ I J z hcentre hpair hregular
  apply (Ideal.eq_top_iff_one _).mpr
  rw [← ha]
  exact Ideal.mem_map_of_mem φ (Ideal.mem_colon_span_singleton.mpr haz)

/-- On a paired Cartier chart, the slice image avoids the reduced strict
transform of the first branch divisor. -/
theorem s2e_paired_chart_strict_branch_avoidance
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ) (I J : Ideal R) (z : R)
    (hcentre : I ⊔ J = Ideal.span {z})
    (hpair : Ideal.map φ I = Ideal.map φ J)
    (hregular : Function.Injective (fun a : S => a * φ z)) :
    Disjoint (Set.range (PrimeSpectrum.comap φ))
      (closure (PrimeSpectrum.zeroLocus (I : Set R) \ PrimeSpectrum.zeroLocus ({z} : Set R))) := by
  obtain ⟨a, ha, haz⟩ := s2e_paired_chart_unit_factor φ hφ I J z hcentre hpair hregular
  have hsubset :
      PrimeSpectrum.zeroLocus (I : Set R) \ PrimeSpectrum.zeroLocus ({z} : Set R) ⊆
        PrimeSpectrum.zeroLocus ({a} : Set R) := by
    intro p hp
    have hprod : a * z ∈ p.asIdeal := hp.1 haz
    have hnz : z ∉ p.asIdeal := fun hz => hp.2 (Set.singleton_subset_iff.mpr hz)
    exact Set.singleton_subset_iff.mpr ((p.isPrime.mem_or_mem hprod).resolve_right hnz)
  have hclosure := (PrimeSpectrum.isClosed_zeroLocus ({a} : Set R)).closure_subset_iff.mpr hsubset
  apply Set.disjoint_left.mpr
  rintro _ ⟨p, rfl⟩ hx
  have hmem := hclosure hx
  have ha_mem := hmem (Set.mem_singleton a)
  change φ a ∈ p.asIdeal at ha_mem
  rw [ha] at ha_mem
  exact p.isPrime.one_notMem ha_mem

/-- The slice avoids both strict branch transforms in the paired chart. -/
theorem s2e_paired_chart_both_branches_avoidance
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ) (I J : Ideal R) (z : R)
    (hcentre : I ⊔ J = Ideal.span {z})
    (hpair : Ideal.map φ I = Ideal.map φ J)
    (hregular : Function.Injective (fun a : S => a * φ z)) :
    Disjoint (Set.range (PrimeSpectrum.comap φ))
      (closure (PrimeSpectrum.zeroLocus (I : Set R) \ PrimeSpectrum.zeroLocus ({z} : Set R)) ∪
        closure (PrimeSpectrum.zeroLocus (J : Set R) \ PrimeSpectrum.zeroLocus ({z} : Set R))) := by
  apply disjoint_sup_right.mpr
  constructor
  · exact s2e_paired_chart_strict_branch_avoidance φ hφ I J z hcentre hpair hregular
  · exact s2e_paired_chart_strict_branch_avoidance φ hφ J I z
      (by rw [sup_comm]; exact hcentre) hpair.symm hregular

end HodgeLean.Foundations.Program
