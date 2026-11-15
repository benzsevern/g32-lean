import HodgeLean.Foundations.Program.G32Native.PairedC3BinomialSequence
import HodgeLean.Foundations.Program.G32Native.PairedC3AdaptedEquation

/-! # Regularity in the original supplied Rees chart -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open Polynomial RingTheory.Sequence
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- An adapted coordinate system gives regular total-transform equations
in the original Rees chart, using its original coefficient map and ratio.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8. -/
theorem paired_c3_supplied_chart_sequence
    {k A B σ : Type u} [CommRing k] [CommRing A] [CommRing B] [DecidableEq σ]
    [Algebra (MvPolynomial σ k) A] [Algebra.Etale (MvPolynomial σ k) A]
    (f : A →+* B) (u v c : A) (s : B)
    (hsurj : Function.Surjective (eval₂RingHom f s))
    (hker : RingHom.ker (eval₂RingHom f s) = Ideal.span {C u - X * C v})
    (a b : σ) (hab : a ≠ b)
    (hu : u - c * v = algebraMap (MvPolynomial σ k) A (MvPolynomial.X a))
    (hv : v = algebraMap (MvPolynomial σ k) A (MvPolynomial.X b))
    (l : List σ) (hl : l.Nodup) (ha : a ∉ l) (hb : b ∉ l) :
    IsWeaklyRegular B
      (l.map (fun j => f (algebraMap (MvPolynomial σ k) A (MvPolynomial.X j))) ++
        [f (u - c * v)]) := by
  let g := algebraMap (MvPolynomial σ k) A
  have hs := paired_c3_adapted_surjective f s c hsurj
  have hk := paired_c3_adapted_kernel f u v c s hker
  rw [hu, hv] at hk
  let e := pairedC3ReesEquationEquiv f (g (MvPolynomial.X a))
    (g (MvPolynomial.X b)) (s - f c) hs hk
  let q := Ideal.Quotient.mk (Ideal.span
    {C (g (MvPolynomial.X a)) - X * C (g (MvPolynomial.X b))})
  let rs := l.map (fun j => q (C (g (MvPolynomial.X j)))) ++
    [q (C (g (MvPolynomial.X a)))]
  have hreg : IsWeaklyRegular _ rs := paired_c3_binomial_total_sequence
    (k := k) (R := A) a b hab l hl ha hb
  letI := RingHomInvPair.of_ringEquiv e
  letI := RingHomInvPair.of_ringEquiv_symm e
  have h := (e.toSemilinearEquiv.isWeaklyRegular_congr' rs).mp hreg
  have he (r : A) : e (q (C r)) = f r :=
    paired_c3_rees_equation_constants f _ _ _ hs hk r
  rw [hu]
  simpa only [rs, List.map_append, List.map_map, List.map_cons, List.map_nil,
    Function.comp_def, RingEquiv.coe_toRingHom, he] using h

#print axioms paired_c3_supplied_chart_sequence
end HodgeLean.Foundations.Program.G32Native
