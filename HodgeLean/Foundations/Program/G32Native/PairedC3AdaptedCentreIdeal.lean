import Mathlib.RingTheory.Ideal.Span

/-! # The centre on a slice with an adapted branch difference -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program.G32Native

/-- Modulo the slice ideal, an adapted branch difference eliminates the
first branch from the ideal of the centre-slice intersection.
Source: Hartshorne, Algebraic Geometry, II.5, affine ideal arithmetic. -/
theorem paired_c3_adapted_centre_ideal
    {A : Type*} [CommRing A] (I : Ideal A) (u v a : A) (h : u - a * v ∈ I) :
    I ⊔ (Ideal.span {u} ⊔ Ideal.span {v}) = I ⊔ Ideal.span {v} := by
  have hd : Ideal.span {u - a * v} ≤ I :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h)
  have hp : Ideal.span {u} ⊔ Ideal.span {v} =
      Ideal.span {u - a * v} ⊔ Ideal.span {v} := by
    rw [← Ideal.span_union, Set.singleton_union,
      ← Ideal.span_union, Set.singleton_union, Ideal.span_pair_sub_mul_right]
  rw [hp, ← sup_assoc, sup_eq_left.mpr hd]

#print axioms paired_c3_adapted_centre_ideal
end HodgeLean.Foundations.Program.G32Native
