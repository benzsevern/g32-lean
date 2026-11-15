import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChart
import HodgeLean.Foundations.Program.G32Native.PairedLastBlowupRegularSequence
import Mathlib.RingTheory.RingHom.Etale

/-! # Regular node equations in any rank of étale coordinates -/
noncomputable section
set_option maxHeartbeats 200000
open RingTheory.Sequence
namespace HodgeLean.Foundations.Program.G32Native

/-- Distinct transverse coordinates followed by a product of two further
coordinates form a weakly regular sequence in an étale coordinate algebra.
Source: Matsumura, Commutative Ring Theory, §16; Hartshorne, Algebraic
Geometry, II.8, regular sequences under flat base change. -/
theorem paired_c3_etale_node_sequence
    {k A σ : Type*} [CommRing k] [CommRing A]
    (f : k →+* A) (z : σ → A) (het : (MvPolynomial.eval₂Hom f z).Etale)
    (l : List σ) (hl : l.Nodup) (a b : σ) (ha : a ∉ l) (hb : b ∉ l) :
    IsWeaklyRegular A (l.map z ++ [z a * z b]) := by
  letI : Algebra (MvPolynomial σ k) A := (MvPolynomial.eval₂Hom f z).toAlgebra
  letI : Algebra.Etale (MvPolynomial σ k) A := het
  have hreg (j : σ) (hj : j ∉ l) : IsWeaklyRegular A (l.map z ++ [z j]) := by
    have h := (AlgebraicGeometry.RegularPairChart.coordinateSequence_of_flat
      (R := k) (A := A) (l ++ [j]) (by simpa only [List.concat_eq_append] using hl.concat hj)).2
    simpa only [List.map_append, List.map_cons, List.map_nil,
      MvPolynomial.eval₂Hom_X', RingHom.algebraMap_toAlgebra] using h
  obtain ⟨hts, hsa⟩ := (isWeaklyRegular_append_iff A (l.map z) [z a]).mp (hreg a ha)
  obtain ⟨_, hsb⟩ := (isWeaklyRegular_append_iff A (l.map z) [z b]).mp (hreg b hb)
  exact paired_last_first_chart_weaklyRegular (l.map z) (z a) (z b) hts
    ((isWeaklyRegular_singleton_iff _ _).mp hsa)
    ((isWeaklyRegular_singleton_iff _ _).mp hsb)

#print axioms paired_c3_etale_node_sequence
end HodgeLean.Foundations.Program.G32Native
