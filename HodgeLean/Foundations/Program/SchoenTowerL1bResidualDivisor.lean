import Mathlib.RingTheory.Spectrum.Prime.Topology

noncomputable section
set_option maxHeartbeats 400000

namespace HodgeLean.Foundations.Program

/-- Removing a divisor not containing the generic point of a prime divisor leaves a dense subset. -/
theorem s2v_l1b_prime_divisor_dense_off_exceptional
    {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime]
    (e : R) (he : e ∉ P) :
    closure (PrimeSpectrum.zeroLocus (P : Set R) \
      PrimeSpectrum.zeroLocus {e}) = PrimeSpectrum.zeroLocus (P : Set R) := by
  apply le_antisymm
  · exact (PrimeSpectrum.isClosed_zeroLocus _).closure_subset_iff.mpr Set.diff_subset
  · let p : PrimeSpectrum R := ⟨P, inferInstance⟩
    have hp : p ∈ PrimeSpectrum.zeroLocus (P : Set R) \
        PrimeSpectrum.zeroLocus {e} := by
      exact ⟨Set.Subset.refl _, fun h => he (h (Set.mem_singleton e))⟩
    have hsingleton : ({p} : Set (PrimeSpectrum R)) ⊆
        PrimeSpectrum.zeroLocus (P : Set R) \ PrimeSpectrum.zeroLocus {e} :=
      Set.singleton_subset_iff.mpr hp
    simpa only [PrimeSpectrum.closure_singleton] using closure_mono hsingleton

/-- In a chart with total equation `s * e`, the reduced residual divisor has equation `s`.
The prime condition and `e ∉ (s)` preserve the residual component when the exceptional divisor is removed. -/
theorem s2v_l1b_residual_prime_equation
    {R : Type*} [CommRing R] (s e : R)
    [hs : (Ideal.span {s}).IsPrime] (he : e ∉ Ideal.span {s}) :
    PrimeSpectrum.vanishingIdeal
      (closure (PrimeSpectrum.zeroLocus {s * e} \
        PrimeSpectrum.zeroLocus {e})) = Ideal.span {s} := by
  have hsets : PrimeSpectrum.zeroLocus {s * e} \
      PrimeSpectrum.zeroLocus {e} =
      PrimeSpectrum.zeroLocus (Ideal.span {s} : Set R) \
        PrimeSpectrum.zeroLocus {e} := by
    rw [PrimeSpectrum.zeroLocus_singleton_mul, PrimeSpectrum.zeroLocus_span]
    exact Set.union_sdiff_right
  rw [hsets, s2v_l1b_prime_divisor_dense_off_exceptional (Ideal.span {s}) e he,
    PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hs.isRadical.radical]

/-- A prime divisor remains dense after removing any centre not containing its generic point. -/
theorem s2v_l1b_prime_divisor_dense_off_centre
    {R : Type*} [CommRing R] (P I : Ideal R) [P.IsPrime]
    (hI : ¬ I ≤ P) :
    closure (PrimeSpectrum.zeroLocus (P : Set R) \
      PrimeSpectrum.zeroLocus (I : Set R)) = PrimeSpectrum.zeroLocus (P : Set R) := by
  apply le_antisymm
  · exact (PrimeSpectrum.isClosed_zeroLocus _).closure_subset_iff.mpr Set.sdiff_subset
  · let p : PrimeSpectrum R := ⟨P, inferInstance⟩
    have hp : p ∈ PrimeSpectrum.zeroLocus (P : Set R) \
        PrimeSpectrum.zeroLocus (I : Set R) := ⟨Set.Subset.refl _, hI⟩
    have hsingleton : ({p} : Set (PrimeSpectrum R)) ⊆
        PrimeSpectrum.zeroLocus (P : Set R) \ PrimeSpectrum.zeroLocus (I : Set R) :=
      Set.singleton_subset_iff.mpr hp
    simpa only [PrimeSpectrum.closure_singleton] using closure_mono hsingleton

end HodgeLean.Foundations.Program
