import Mathlib.RingTheory.Ideal.Maps

/-! # Lifting a branch ratio from a quotient slice

Equality of the two principal restriction ideals supplies an actual
coefficient in the ambient ring. This is an ideal calculation, including
multiplicities, over any commutative coefficient ring.
-/
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native

/-- A coefficient relating the two restricted branch equations lifts across
a surjective section map, leaving an element of the actual slice kernel.
Source: Hartshorne, Algebraic Geometry, II.3, quotient affine subschemes. -/
theorem paired_c3_lift_slice_coefficient
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (u v : A)
    (h : Ideal.span ({f u} : Set B) = Ideal.span {f v}) :
    ∃ a : A, u - a * v ∈ RingHom.ker f := by
  have hu : f u ∈ Ideal.span ({f v} : Set B) :=
    h ▸ Ideal.subset_span (Set.mem_singleton (f u))
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hu
  obtain ⟨a, ha⟩ := hf b
  refine ⟨a, ?_⟩
  rw [RingHom.mem_ker, map_sub, map_mul, ha]
  rw [hb]
  ring

#print axioms paired_c3_lift_slice_coefficient

/-- When the restricted branch parameter is regular, every lifted ratio
has invertible restriction to the slice. Ambient invertibility is not asserted.
Source: Hartshorne, Algebraic Geometry, II.6, local Cartier equations. -/
theorem paired_c3_slice_coefficient_unit
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (u v a : A)
    (h : Ideal.span ({f u} : Set B) = Ideal.span {f v})
    (hreg : Function.Injective (fun b : B => b * f v))
    (ha : f (u - a * v) = 0) : IsUnit (f a) := by
  have hu : f u = f a * f v := by
    rw [map_sub, map_mul, sub_eq_zero] at ha
    exact ha
  have hv : f v ∈ Ideal.span ({f u} : Set B) :=
    h.symm ▸ Ideal.subset_span (Set.mem_singleton (f v))
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hv
  apply isUnit_iff_exists_inv.mpr
  refine ⟨b, hreg ?_⟩
  calc
    (f a * b) * f v = (f a * f v) * b := by ring
    _ = f u * b := by rw [hu]
    _ = f v := hb.symm
    _ = 1 * f v := (one_mul _).symm

#print axioms paired_c3_slice_coefficient_unit
end HodgeLean.Foundations.Program.G32Native
