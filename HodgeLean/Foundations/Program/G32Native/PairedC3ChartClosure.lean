import HodgeLean.Foundations.Program.G32Native.PairedC3DirectChartUnion
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! # The reduced strict component in a retained affine chart -/
noncomputable section
set_option maxHeartbeats 200000
open Polynomial PrimeSpectrum
namespace HodgeLean.Foundations.Program.G32Native

/-- A prime translated-ratio ideal is the reduced closure of the slice
away from the exceptional parameter. This identifies the reduced strict
transform rather than merely a saturation.
Source: Hartshorne, Algebraic Geometry, II.3 and II.7.13. -/
theorem paired_c3_chart_closure
    {B : Type*} [CommRing B] (K : Ideal B) (s w : B)
    (hQ : (K ⊔ Ideal.span {w}).IsPrime)
    (hs : s ∉ K ⊔ Ideal.span {w}) (hmul : s * w ∈ K) :
    closure (zeroLocus (K : Set B) \ zeroLocus ({s} : Set B)) =
      zeroLocus ((K ⊔ Ideal.span {w} : Ideal B) : Set B) := by
  let q : PrimeSpectrum B := ⟨K ⊔ Ideal.span {w}, hQ⟩
  apply Set.Subset.antisymm
  · apply (isClosed_zeroLocus _).closure_subset_iff.mpr
    intro p hp
    change K ⊔ Ideal.span {w} ≤ p.asIdeal
    have hpK : K ≤ p.asIdeal := hp.1
    apply sup_le hpK
    apply Ideal.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    have hsmem : s ∉ p.asIdeal := by
      intro h
      exact hp.2 (by intro x hx; obtain rfl := Set.mem_singleton_iff.mp hx; exact h)
    exact (p.isPrime.mem_or_mem (hpK hmul)).resolve_left hsmem
  · have hq : q ∈ zeroLocus (K : Set B) \ zeroLocus ({s} : Set B) := by
      refine ⟨?_, ?_⟩
      · exact (show K ≤ K ⊔ Ideal.span {w} from le_sup_left)
      · intro h
        exact hs (h (Set.mem_singleton _))
    have hsub : ({q} : Set (PrimeSpectrum B)) ⊆
        zeroLocus (K : Set B) \ zeroLocus ({s} : Set B) := Set.singleton_subset_iff.mpr hq
    simpa only [PrimeSpectrum.closure_singleton, q] using closure_mono hsub

#print axioms paired_c3_chart_closure
/-- For an integral slice, the reduced strict-transform ideal on a
supplied Rees chart is exactly the translated-ratio ideal.
Source: Hartshorne, Algebraic Geometry, II.3 and II.7.13. -/
theorem paired_c3_rees_strict_ideal
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (u v a : A) (t : B) (I : Ideal A) [I.IsPrime]
    (hs : Function.Surjective (eval₂RingHom f t))
    (hk : RingHom.ker (eval₂RingHom f t) = Ideal.span {C v - X * C u})
    (ha : v - a * u ∈ I) (hu : u ∉ I) :
    vanishingIdeal (closure (zeroLocus ((I.map f : Ideal B) : Set B) \
      zeroLocus ({f u} : Set B))) = I.map f ⊔ Ideal.span {t - f a} := by
  obtain ⟨g, hf, ht⟩ := paired_c3_chart_retraction f u v a t I hs hk ha
  have hker := paired_c3_chart_retraction_kernel f a t I hs g hf ht
  have hQ : (I.map f ⊔ Ideal.span {t - f a}).IsPrime := by
    rw [← hker]
    exact RingHom.ker_isPrime g
  have hnon : f u ∉ I.map f ⊔ Ideal.span {t - f a} := by
    rw [← hker]
    intro h
    apply hu
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hfu := DFunLike.congr_fun hf u
    exact hfu.symm.trans h
  have hrel : f v = t * f u := by
    have h : C v - X * C u ∈ RingHom.ker (eval₂RingHom f t) := by
      rw [hk]
      exact Ideal.subset_span (Set.mem_singleton _)
    change eval₂ f t (C v - X * C u) = 0 at h
    simpa only [eval₂_sub, eval₂_C, eval₂_mul, eval₂_X, sub_eq_zero] using h
  have hmul : f u * (t - f a) ∈ I.map f := by
    have heq : f u * (t - f a) = f (v - a * u) := by
      rw [map_sub, map_mul, hrel]
      ring
    rw [heq]
    exact Ideal.mem_map_of_mem f ha
  rw [paired_c3_chart_closure (I.map f) (f u) (t - f a) hQ hnon hmul,
    vanishingIdeal_zeroLocus_eq_radical, hQ.isRadical.radical]

#print axioms paired_c3_rees_strict_ideal
end HodgeLean.Foundations.Program.G32Native
