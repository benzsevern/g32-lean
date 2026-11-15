import HodgeLean.Foundations.Program.SchoenCyclePairedChart
import Mathlib.LinearAlgebra.Basis.Basic

/-! # Local freeness and regular parameters for paired slices
The ideal-module equivalence provides a regular principal generator.
-/

namespace HodgeLean.Foundations.Program

/-- An ideal isomorphic to its coefficient ring has a principal generator
whose multiplication map on the ring is injective. -/
theorem s2e_free_ideal_regular_generator
    {R : Type*} [CommRing R] (I : Ideal R) (e : I ≃ₗ[R] R) :
    ∃ z : R, I = Ideal.span {z} ∧ Function.Injective (fun a : R => a * z) := by
  let z : R := (e.symm 1 : I)
  have hcoord (a : R) : (e.symm a : R) = a * z := by
    have he := congrArg Subtype.val (e.symm.map_smul a (1 : R))
    change (e.symm (a * 1) : R) = a * z at he
    simpa only [mul_one] using he
  refine ⟨z, le_antisymm ?_ ?_, ?_⟩
  · intro a ha
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨e ⟨a, ha⟩, ?_⟩
    rw [← hcoord]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨a, ha⟩)
  · apply Ideal.span_le.mpr
    exact Set.singleton_subset_iff.mpr (e.symm 1).property
  · intro a b hab
    apply e.symm.injective
    apply Subtype.ext
    simpa only [hcoord] using hab

/-- Every generator of a principal ideal that is free of rank one is a
regular parameter, including over rings with zero divisors. -/
theorem s2e_principal_free_ideal_regular
    {R : Type*} [CommRing R] (z : R)
    (e : (Ideal.span {z}) ≃ₗ[R] R) :
    Function.Injective (fun a : R => a * z) := by
  obtain ⟨w, hw, hregular⟩ := s2e_free_ideal_regular_generator (Ideal.span {z}) e
  have hwmem : w ∈ Ideal.span {z} := by
    rw [hw]
    exact Ideal.subset_span (Set.mem_singleton w)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hwmem
  intro a b hab
  apply hregular
  rw [← hc]
  calc
    a * (c * z) = c * (a * z) := by rw [← mul_assoc, mul_comm a c, mul_assoc]
    _ = c * (b * z) := congrArg (c * ·) hab
    _ = b * (c * z) := by rw [← mul_assoc, mul_comm c b, mul_assoc]

/-- Local freeness of the restricted centre makes the exceptional parameter
regular on the affine slice. -/
theorem s2e_paired_chart_regular_of_free_restriction
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (I J : Ideal R) (z : R)
    (hcentre : I ⊔ J = Ideal.span {z})
    (hfree : Nonempty ((Ideal.map φ (I ⊔ J)) ≃ₗ[S] S)) :
    Function.Injective (fun a : S => a * φ z) := by
  rw [hcentre, Ideal.map_span, Set.image_singleton] at hfree
  obtain ⟨e⟩ := hfree
  exact s2e_principal_free_ideal_regular (φ z) e

/-- A paired Cartier slice avoids both strict branch loci using only the
local ideal-module freeness test for its restricted centre. -/
theorem s2e_paired_cartier_chart_both_branches_avoidance
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ) (I J : Ideal R) (z : R)
    (hcentre : I ⊔ J = Ideal.span {z})
    (hpair : Ideal.map φ I = Ideal.map φ J)
    (hfree : Nonempty ((Ideal.map φ (I ⊔ J)) ≃ₗ[S] S)) :
    Disjoint (Set.range (PrimeSpectrum.comap φ))
      (closure (PrimeSpectrum.zeroLocus (I : Set R) \ PrimeSpectrum.zeroLocus ({z} : Set R)) ∪
        closure (PrimeSpectrum.zeroLocus (J : Set R) \ PrimeSpectrum.zeroLocus ({z} : Set R))) := by
  exact s2e_paired_chart_both_branches_avoidance φ hφ I J z hcentre hpair
    (s2e_paired_chart_regular_of_free_restriction φ I J z hcentre hfree)

end HodgeLean.Foundations.Program
