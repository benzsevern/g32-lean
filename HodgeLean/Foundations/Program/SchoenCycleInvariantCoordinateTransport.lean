import Mathlib.Algebra.Algebra.Subalgebra.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Comparing two actual invariant coordinate systems preserves the specified ambient pullback values.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_invariant_coordinate_transport_values
    {k A B C : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    (K : Subalgebra k A) (E : B ≃ₐ[k] K) (F : C ≃ₐ[k] K)
    (φ : B →ₐ[k] A) (hE : ∀ z, (E z).val = φ z) :
    ∃ D : B ≃ₐ[k] C, ∀ c, φ (D.symm c) = (F c).val := by
  refine ⟨E.trans F.symm, ?_⟩
  intro c
  rw [← hE]
  change (E (E.symm (F c))).val = (F c).val
  rw [E.apply_symm_apply]

#print axioms s2e_invariant_coordinate_transport_values
end HodgeLean.Foundations.Program
