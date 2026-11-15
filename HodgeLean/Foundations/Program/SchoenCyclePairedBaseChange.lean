import HodgeLean.Foundations.Program.SchoenCyclePairedChart
import Mathlib.RingTheory.Ideal.Operations

/-! # Paired branch avoidance under arbitrary affine base change
Extension of the divided branch ideal suffices for arbitrary ring maps.
-/

namespace HodgeLean.Foundations.Program

/-- The divided branch ideal becomes the unit ideal on a paired Cartier
slice under an arbitrary ring map. -/
theorem s2e_paired_baseChange_colon_map_top
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (I J : Ideal R) (z : R)
    (hcentre : I ⊔ J = Ideal.span {z})
    (hpair : Ideal.map φ I = Ideal.map φ J)
    (hregular : Function.Injective (fun a : S => a * φ z)) :
    Ideal.map φ (I.colon (Ideal.span {z})) = ⊤ := by
  have hz : z ∈ I ⊔ J := by
    rw [hcentre]
    exact Ideal.subset_span (Set.mem_singleton z)
  have hzmap : φ z ∈ Ideal.map φ I := by
    have h := Ideal.mem_map_of_mem φ hz
    rw [Ideal.map_sup, ← hpair, sup_idem] at h
    exact h
  have hle : Ideal.map φ I ≤
      Ideal.map φ (I.colon (Ideal.span {z})) * Ideal.span {φ z} := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have hxspan : x ∈ Ideal.span {z} := by
      rw [← hcentre]
      exact (le_sup_left : I ≤ I ⊔ J) hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hxspan
    apply Ideal.mem_mul_span_singleton.mpr
    refine ⟨φ a, Ideal.mem_map_of_mem φ ?_, ?_⟩
    · apply Ideal.mem_colon_span_singleton.mpr
      rwa [ha]
    · rw [← map_mul, ha]
  obtain ⟨b, hb, hbz⟩ := Ideal.mem_mul_span_singleton.mp (hle hzmap)
  have hb1 : b = 1 := hregular (by simpa only [one_mul] using hbz)
  apply (Ideal.eq_top_iff_one _).mpr
  rwa [hb1] at hb

/-- Arbitrary affine base change preserves paired strict branch avoidance
when the centre parameter remains regular. -/
theorem s2e_paired_baseChange_strict_branch_avoidance
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (I J : Ideal R) (z : R)
    (hcentre : I ⊔ J = Ideal.span {z})
    (hpair : Ideal.map φ I = Ideal.map φ J)
    (hregular : Function.Injective (fun a : S => a * φ z)) :
    Disjoint (Set.range (PrimeSpectrum.comap φ))
      (closure (PrimeSpectrum.zeroLocus (I : Set R) \ PrimeSpectrum.zeroLocus ({z} : Set R))) := by
  have hsubset : PrimeSpectrum.zeroLocus (I : Set R) \ PrimeSpectrum.zeroLocus ({z} : Set R) ⊆
      PrimeSpectrum.zeroLocus (I.colon (Ideal.span {z}) : Set R) := by
    intro p hp a ha
    have hprod : a * z ∈ p.asIdeal := hp.1 (Ideal.mem_colon_span_singleton.mp ha)
    have hnz : z ∉ p.asIdeal := fun hz => hp.2 (Set.singleton_subset_iff.mpr hz)
    exact (p.isPrime.mem_or_mem hprod).resolve_right hnz
  have hclosure := (PrimeSpectrum.isClosed_zeroLocus
    (I.colon (Ideal.span {z}) : Set R)).closure_subset_iff.mpr hsubset
  apply Set.disjoint_left.mpr
  rintro _ ⟨p, rfl⟩ hx
  have hle : Ideal.map φ (I.colon (Ideal.span {z})) ≤ p.asIdeal := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    exact hclosure hx ha
  rw [s2e_paired_baseChange_colon_map_top φ I J z hcentre hpair hregular] at hle
  exact p.isPrime.one_notMem (hle (show (1 : S) ∈ (⊤ : Ideal S) from trivial))

end HodgeLean.Foundations.Program
