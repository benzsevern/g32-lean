import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.Span

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A unit relation after faithfully flat extension gives equality of the original principal ideals.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 6;
Mathlib, Ideal.comap_map_eq_self_of_faithfullyFlat. -/
theorem s2e_faithfullyFlat_unit_principal_contraction
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.FaithfullyFlat R A] (s t : R) (u : A) (hu : IsUnit u)
    (h : algebraMap R A s = u * algebraMap R A t) :
    Ideal.span {s} = Ideal.span {t} := by
  apply Ideal.map_injective_of_faithfullyFlat (B := A)
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, h]
  exact Ideal.span_singleton_mul_left_unit hu _

#print axioms s2e_faithfullyFlat_unit_principal_contraction
end HodgeLean.Foundations.Program
