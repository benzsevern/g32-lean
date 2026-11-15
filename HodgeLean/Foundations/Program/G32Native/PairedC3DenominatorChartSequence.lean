import HodgeLean.Foundations.Program.G32Native.PairedC3BinomialSequence
import HodgeLean.Foundations.Program.G32Native.PairedC3ReesEquationIso

/-! # Regular coordinate families avoiding the numerator of a Rees chart -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial RingTheory.Sequence
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Coordinates other than the replaced numerator retain their regular
sequence on a binomial chart; the denominator coordinate is allowed.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8. -/
theorem paired_c3_binomial_unchanged_sequence
    {K A σ : Type} [CommRing K] [CommRing A] [DecidableEq σ]
    [Algebra (MvPolynomial σ K) A] [Algebra.Etale (MvPolynomial σ K) A]
    (a b : σ) (hab : a ≠ b) {n : ℕ} (t : Fin n ↪ σ)
    (ha : a ∉ Set.range t) :
    let g := algebraMap (MvPolynomial σ K) A
    let Q := s2v_L1bChart (g (MvPolynomial.X a)) (g (MvPolynomial.X b))
    let q := Ideal.Quotient.mk (Ideal.span
      {C (g (MvPolynomial.X a)) - Polynomial.X * C (g (MvPolynomial.X b))})
    IsWeaklyRegular Q (List.ofFn fun j => q (C (g (MvPolynomial.X (t j))))) := by
  dsimp only
  let g := algebraMap (MvPolynomial σ K) A
  let Q := s2v_L1bChart (g (MvPolynomial.X a)) (g (MvPolynomial.X b))
  let q := Ideal.Quotient.mk (Ideal.span
    {C (g (MvPolynomial.X a)) - Polynomial.X * C (g (MvPolynomial.X b))})
  obtain ⟨z, het, hz⟩ := s2v_l1b_etale_binomial_chart (k := K) (R := A) a b hab
  let f := (q.comp C).comp (g.comp MvPolynomial.C)
  letI : Algebra (MvPolynomial σ K) Q := (MvPolynomial.eval₂Hom f z).toAlgebra
  letI : Algebra.Etale (MvPolynomial σ K) Q := het
  have H := (AlgebraicGeometry.RegularPairChart.coordinateSequence_of_flat
    (R := K) (A := Q) (List.ofFn t) (List.nodup_ofFn.mpr t.injective)).2
  have hc (j : σ) : algebraMap (MvPolynomial σ K) Q (MvPolynomial.X j) = z j := by
    change (MvPolynomial.eval₂Hom f z) (MvPolynomial.X j) = z j
    exact MvPolynomial.eval₂Hom_X' f z j
  simp_rw [hc] at H
  have hreg : IsWeaklyRegular Q (List.ofFn fun j => z (t j)) := by
    simpa only [List.map_ofFn, Function.comp_def] using H
  have hcoord (j : Fin n) : q (C (g (MvPolynomial.X (t j)))) = z (t j) := by
    have hne : t j ≠ a := fun h => ha ⟨j, h⟩
    simpa only [if_neg hne] using hz (t j)
  change IsWeaklyRegular Q (List.ofFn fun j => q (C (g (MvPolynomial.X (t j)))))
  simp_rw [hcoord]
  exact hreg

#print axioms paired_c3_binomial_unchanged_sequence

/-- The unchanged coordinate family remains regular in any supplied chart
with the specified original coefficient map and polynomial kernel.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8. -/
theorem paired_c3_supplied_unchanged_sequence
    {K A B σ : Type} [CommRing K] [CommRing A] [CommRing B] [DecidableEq σ]
    [Algebra (MvPolynomial σ K) A] [Algebra.Etale (MvPolynomial σ K) A]
    (f : A →+* B) (a b : σ) (hab : a ≠ b) (s : B)
    (hsurj : Function.Surjective (eval₂RingHom f s))
    (hker : RingHom.ker (eval₂RingHom f s) = Ideal.span
      {C (algebraMap (MvPolynomial σ K) A (MvPolynomial.X a)) - Polynomial.X *
        C (algebraMap (MvPolynomial σ K) A (MvPolynomial.X b))})
    {n : ℕ} (t : Fin n ↪ σ) (ha : a ∉ Set.range t) :
    IsWeaklyRegular B (List.ofFn fun j =>
      f (algebraMap (MvPolynomial σ K) A (MvPolynomial.X (t j)))) := by
  let g := algebraMap (MvPolynomial σ K) A
  let q := Ideal.Quotient.mk (Ideal.span
    {C (g (MvPolynomial.X a)) - Polynomial.X * C (g (MvPolynomial.X b))})
  let e := pairedC3ReesEquationEquiv f (g (MvPolynomial.X a))
    (g (MvPolynomial.X b)) s hsurj hker
  letI := RingHomInvPair.of_ringEquiv e
  letI := RingHomInvPair.of_ringEquiv_symm e
  have hreg := paired_c3_binomial_unchanged_sequence (K := K) (A := A) a b hab t ha
  have H := (e.toSemilinearEquiv.isWeaklyRegular_congr'
    (List.ofFn fun j => q (C (g (MvPolynomial.X (t j)))))).mp hreg
  have he (r : A) : e (q (C r)) = f r :=
    paired_c3_rees_equation_constants f _ _ _ hsurj hker r
  simpa only [List.map_ofFn, Function.comp_def, RingEquiv.coe_toRingHom, he] using H

#print axioms paired_c3_supplied_unchanged_sequence
end HodgeLean.Foundations.Program.G32Native
