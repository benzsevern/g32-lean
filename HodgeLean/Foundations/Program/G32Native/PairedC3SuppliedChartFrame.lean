import HodgeLean.Foundations.Program.G32Native.PairedC3SuppliedChartSequence
import HodgeLean.Foundations.Program.G32Native.PairedC3AffineFrame

/-! # Finite conormal frames in the supplied branch chart -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial RingTheory.Sequence CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The transverse equations followed by the adapted branch difference
form a finite regular family in the supplied chart.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8. -/
theorem paired_c3_supplied_chart_finite_sequence
    {k A B σ : Type} [CommRing k] [CommRing A] [CommRing B] [DecidableEq σ]
    [Algebra (MvPolynomial σ k) A] [Algebra.Etale (MvPolynomial σ k) A]
    (f : A →+* B) (u v c : A) (s : B)
    (hsurj : Function.Surjective (eval₂RingHom f s))
    (hker : RingHom.ker (eval₂RingHom f s) = Ideal.span {C u - X * C v})
    (a b : σ) (hab : a ≠ b)
    (hu : u - c * v = algebraMap (MvPolynomial σ k) A (MvPolynomial.X a))
    (hv : v = algebraMap (MvPolynomial σ k) A (MvPolynomial.X b))
    {n : ℕ} (t : Fin n ↪ σ) (ha : a ∉ Set.range t) (hb : b ∉ Set.range t) :
    IsWeaklyRegular B (List.ofFn (Fin.append
      (fun j => f (algebraMap (MvPolynomial σ k) A (MvPolynomial.X (t j))))
      (fun _ : Fin 1 => f (u - c * v)))) := by
  rw [List.ofFn_fin_append]
  simpa only [List.ofFn_succ, List.ofFn_zero, List.ofFn_comp', List.map_map, Function.comp_def]
    using paired_c3_supplied_chart_sequence f u v c s hsurj hker a b hab hu hv
      (List.ofFn t) (List.nodup_ofFn.mpr t.injective)
      (by simpa only [List.mem_ofFn, Set.mem_range] using ha)
      (by simpa only [List.mem_ofFn, Set.mem_range] using hb)

#print axioms paired_c3_supplied_chart_finite_sequence

/-- The adapted equations in the supplied Rees chart give the conormal
sheaf of their actual quotient spectrum its finite free frame.
Source: Hartshorne, Algebraic Geometry, II.5, II.7.13 and II.8. -/
def pairedC3SuppliedChartConormalFrame
    {k A B σ : Type} [CommRing k] [CommRing A] [CommRing B] [DecidableEq σ]
    [Algebra (MvPolynomial σ k) A] [Algebra.Etale (MvPolynomial σ k) A]
    (f : A →+* B) (u v c : A) (s : B)
    (hsurj : Function.Surjective (eval₂RingHom f s))
    (hker : RingHom.ker (eval₂RingHom f s) = Ideal.span {C u - X * C v})
    (a b : σ) (hab : a ≠ b)
    (hu : u - c * v = algebraMap (MvPolynomial σ k) A (MvPolynomial.X a))
    (hv : v = algebraMap (MvPolynomial σ k) A (MvPolynomial.X b))
    {n : ℕ} (t : Fin n ↪ σ) (ha : a ∉ Set.range t) (hb : b ∉ Set.range t) :
    let z := Fin.append
      (fun j => f (algebraMap (MvPolynomial σ k) A (MvPolynomial.X (t j))))
      (fun _ : Fin 1 => f (u - c * v))
    let I := Ideal.span (Set.range z)
    HodgeLean.Foundations.Program.s2c_conormal
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≅
      (SheafOfModules.free (R := (Spec (CommRingCat.of (B ⧸ I))).ringCatSheaf)
        (Fin (n + 1)) : (Spec (CommRingCat.of (B ⧸ I))).Modules) :=
  pairedC3AffineConormalFrame _
    (paired_c3_supplied_chart_finite_sequence f u v c s hsurj hker a b hab hu hv t ha hb)

#print axioms pairedC3SuppliedChartConormalFrame
end HodgeLean.Foundations.Program.G32Native
