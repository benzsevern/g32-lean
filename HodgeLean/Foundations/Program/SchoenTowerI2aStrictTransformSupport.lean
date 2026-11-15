import HodgeLean.Foundations.Program.SchoenCycleSliceHelpers
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Ideal.Maximal

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Removing an exceptional section outside a prime divisor's generic point
preserves that divisor after taking the topological closure.
Source: Hartshorne, Algebraic Geometry, II.3, generic points of integral affine subschemes. -/
theorem s2v_i2a_prime_divisor_removed_support
    {R : Type*} [CommRing R] (I : Ideal R) [I.IsPrime] (x : R) (hx : x ∉ I) :
    closure (PrimeSpectrum.zeroLocus (I : Set R) \ PrimeSpectrum.zeroLocus ({x} : Set R)) =
      PrimeSpectrum.zeroLocus (I : Set R) := by
  apply subset_antisymm
  · exact (PrimeSpectrum.isClosed_zeroLocus _).closure_subset_iff.mpr Set.diff_subset
  · let p : PrimeSpectrum R := ⟨I, inferInstance⟩
    have hp : p ∈ PrimeSpectrum.zeroLocus (I : Set R) \ PrimeSpectrum.zeroLocus ({x} : Set R) := by
      refine ⟨fun a ha => ha, ?_⟩
      intro H
      exact hx (H (Set.mem_singleton x))
    have hs : ({p} : Set (PrimeSpectrum R)) ⊆
        PrimeSpectrum.zeroLocus (I : Set R) \ PrimeSpectrum.zeroLocus ({x} : Set R) :=
      Set.singleton_subset_iff.mpr hp
    have H := closure_mono hs
    rw [PrimeSpectrum.closure_singleton] at H
    exact H

/-- A coordinate divisor is recovered after removing a distinct coordinate divisor.
Source: Hartshorne, Algebraic Geometry, II.3, generic points of integral affine subschemes. -/
theorem s2v_i2a_coordinate_divisor_removed_support
    {A : Type*} [CommRing A] [IsDomain A] {ι : Type*} (i j : ι) (hij : i ≠ j) :
    closure (PrimeSpectrum.zeroLocus ({MvPolynomial.X j} : Set (MvPolynomial ι A)) \
      PrimeSpectrum.zeroLocus ({MvPolynomial.X i} : Set (MvPolynomial ι A))) =
      PrimeSpectrum.zeroLocus ({MvPolynomial.X j} : Set (MvPolynomial ι A)) := by
  let I : Ideal (MvPolynomial ι A) := Ideal.span {MvPolynomial.X j}
  letI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime MvPolynomial.X_prime
  have hx : (MvPolynomial.X i : MvPolynomial ι A) ∉ I := by
    rw [Ideal.mem_span_singleton, MvPolynomial.X_dvd_X]
    exact Ne.symm hij
  simpa only [I, PrimeSpectrum.zeroLocus_span] using
    s2v_i2a_prime_divisor_removed_support I (MvPolynomial.X i) hx

/-- The reduced branch supports on the first paired polynomial blowup chart
are empty for the exceptional branch and coordinate divisors for all other branches.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13, affine blowup charts. -/
theorem s2v_i2a_paired_polynomial_strict_support
    {A : Type*} [CommRing A] [IsDomain A] {ι : Type*} [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) (k : ι) :
    let P := MvPolynomial ι A
    let b : P →+* P := MvPolynomial.eval₂Hom MvPolynomial.C
      (fun l => if l = j then MvPolynomial.X i * MvPolynomial.X j else MvPolynomial.X l)
    closure (PrimeSpectrum.comap b ⁻¹'
      (PrimeSpectrum.zeroLocus ({MvPolynomial.X k} : Set P) \
       PrimeSpectrum.zeroLocus ({MvPolynomial.X i, MvPolynomial.X j} : Set P))) =
      if k = i then ∅ else PrimeSpectrum.zeroLocus ({MvPolynomial.X k} : Set P) := by
  classical
  intro P b
  have hb (l : ι) : b (MvPolynomial.X l) =
      if l = j then MvPolynomial.X i * MvPolynomial.X j else MvPolynomial.X l := by
    simp [b, MvPolynomial.eval₂Hom]
  have hi : b (MvPolynomial.X i) = MvPolynomial.X i := by simp [hb, hij]
  have hj : b (MvPolynomial.X j) = MvPolynomial.X i * MvPolynomial.X j := by simp [hb]
  have hpre : PrimeSpectrum.comap b ⁻¹'
      PrimeSpectrum.zeroLocus ({MvPolynomial.X i, MvPolynomial.X j} : Set P) =
      PrimeSpectrum.zeroLocus ({MvPolynomial.X i} : Set P) := by
    ext p
    simp only [Set.mem_preimage, PrimeSpectrum.mem_zeroLocus, Set.insert_subset_iff,
      Set.singleton_subset_iff, PrimeSpectrum.comap_asIdeal]
    change (b (MvPolynomial.X i) ∈ p.asIdeal ∧ b (MvPolynomial.X j) ∈ p.asIdeal) ↔
      MvPolynomial.X i ∈ p.asIdeal
    rw [hi, hj]
    exact ⟨And.left, fun h => ⟨h, p.asIdeal.mul_mem_right _ h⟩⟩
  have hbranch : PrimeSpectrum.comap b ⁻¹'
      PrimeSpectrum.zeroLocus ({MvPolynomial.X k} : Set P) =
      PrimeSpectrum.zeroLocus ({b (MvPolynomial.X k)} : Set P) := by
    ext p
    simp only [Set.mem_preimage, PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff,
      PrimeSpectrum.comap_asIdeal]
    rfl
  rw [Set.preimage_sdiff, hpre, hbranch]
  by_cases hki : k = i
  · subst k
    simp [hi]
  · rw [if_neg hki]
    by_cases hkj : k = j
    · subst k
      rw [hj, PrimeSpectrum.zeroLocus_singleton_mul]
      have hset (S T : Set (PrimeSpectrum P)) : (S ∪ T) \ S = T \ S := by
        ext p
        simp only [Set.mem_sdiff, Set.mem_union]
        tauto
      rw [hset]
      exact s2v_i2a_coordinate_divisor_removed_support i j hij
    · rw [hb, if_neg hkj]
      exact s2v_i2a_coordinate_divisor_removed_support i k (Ne.symm hki)

/-- The reduced ideals of the transformed polynomial branches are the unit ideal
for the exceptional branch and the specified principal coordinate ideals otherwise.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13, reduced strict transforms. -/
theorem s2v_i2a_paired_polynomial_strict_ideal
    {A : Type*} [CommRing A] [IsDomain A] {ι : Type*} [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) (k : ι) :
    let P := MvPolynomial ι A
    let b : P →+* P := MvPolynomial.eval₂Hom MvPolynomial.C
      (fun l => if l = j then MvPolynomial.X i * MvPolynomial.X j else MvPolynomial.X l)
    PrimeSpectrum.vanishingIdeal (closure (PrimeSpectrum.comap b ⁻¹'
      (PrimeSpectrum.zeroLocus ({MvPolynomial.X k} : Set P) \
       PrimeSpectrum.zeroLocus ({MvPolynomial.X i, MvPolynomial.X j} : Set P)))) =
      if k = i then ⊤ else Ideal.span {MvPolynomial.X k} := by
  classical
  intro P b
  rw [s2v_i2a_paired_polynomial_strict_support i j hij k]
  split_ifs with hki
  · exact PrimeSpectrum.vanishingIdeal_empty
  · rw [← PrimeSpectrum.zeroLocus_span, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
    let I : Ideal P := Ideal.span {MvPolynomial.X k}
    letI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime MvPolynomial.X_prime
    exact (Ideal.IsPrime.isRadical (inferInstance : I.IsPrime)).radical

end HodgeLean.Foundations.Program
