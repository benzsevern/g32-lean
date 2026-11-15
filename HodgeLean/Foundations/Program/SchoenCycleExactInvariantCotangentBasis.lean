import HodgeLean.Foundations.Program.SchoenCycleExactFormalCoordinateFunctions

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Actual functions with matching exact coefficient values in a common formal invariant algebra form the actual local cotangent basis.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_exact_invariant_coefficient_cotangent_basis
    {k T R σ : Type*} [Field k] [CommRing T] [CommRing R]
    [Algebra k T] [Algebra k R] [IsLocalRing T] [IsNoetherianRing T]
    [IsLocalRing R] [Fintype σ]
    (K : Subalgebra k (AdicCompletion (IsLocalRing.maximalIdeal R) R))
    (E : AdicCompletion (IsLocalRing.maximalIdeal T) T ≃ₐ[k] K)
    (F : AdicCompletion (idealOfVars σ k) (MvPolynomial σ k) ≃ₐ[k] K)
    (f : T →ₐ[k] R)
    (hE : ∀ t, (E (AdicCompletion.of (IsLocalRing.maximalIdeal T) T t)).val =
      AdicCompletion.of (IsLocalRing.maximalIdeal R) R (f t))
    (c : σ → T)
    (hF : ∀ i, (F (AdicCompletion.of (idealOfVars σ k) (MvPolynomial σ k) (X i))).val =
      AdicCompletion.of (IsLocalRing.maximalIdeal R) R (f (c i))) :
    ∃ (hc : ∀ i, c i ∈ IsLocalRing.maximalIdeal T)
      (B : Module.Basis σ k (IsLocalRing.maximalIdeal T).Cotangent),
      ∀ i, B i = (IsLocalRing.maximalIdeal T).toCotangent ⟨c i, hc i⟩ := by
  apply s2e_exact_formal_coordinate_functions (E.trans F.symm) c
  intro i
  apply F.injective
  rw [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  exact (hE (c i)).trans (hF i).symm

#print axioms s2e_exact_invariant_coefficient_cotangent_basis
end HodgeLean.Foundations.Program
