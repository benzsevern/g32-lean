import Mathlib.Algebra.Algebra.Subalgebra.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- An actual algebra map compatible with two identifications of the same invariant subalgebra is bijective.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_actual_map_bijective_of_common_invariant_coordinates
    {k A B C : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    (K : Subalgebra k C) (E : A ≃ₐ[k] K) (F : B ≃ₐ[k] K) (f : A →ₐ[k] B)
    (h : ∀ x, (F (f x)).val = (E x).val) : Function.Bijective f := by
  have he (x : A) : F (f x) = E x := Subtype.ext (h x)
  constructor
  · intro x y hxy
    apply E.injective
    rw [← he x, ← he y, hxy]
  · intro y
    refine ⟨E.symm (F y), F.injective ?_⟩
    rw [he, AlgEquiv.apply_symm_apply]

#print axioms s2e_actual_map_bijective_of_common_invariant_coordinates
end HodgeLean.Foundations.Program
