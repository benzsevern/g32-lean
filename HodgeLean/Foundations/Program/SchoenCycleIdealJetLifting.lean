import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Finite approximations preserving membership in a specified ideal -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Surjectivity modulo an ideal lifts every image-ideal element while preserving membership in the original ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.5. -/
theorem s2e_ideal_jet_lift_of_quotient_surjective
    {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A)
    (J : Ideal R) (K : Ideal A)
    (hφ : Function.Surjective ((Ideal.Quotient.mk K).comp φ))
    (r : A) (hr : r ∈ J.map φ) :
    ∃ s ∈ J, r - φ s ∈ K := by
  have hm : Ideal.Quotient.mk K r ∈ J.map ((Ideal.Quotient.mk K).comp φ) := by
    rw [← Ideal.map_map]
    exact Ideal.mem_map_of_mem (Ideal.Quotient.mk K) hr
  obtain ⟨s, hs, he⟩ := (Ideal.mem_map_iff_of_surjective _ hφ).mp hm
  refine ⟨s, hs, ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub]
  exact sub_eq_zero.mpr he.symm

end HodgeLean.Foundations.Program
