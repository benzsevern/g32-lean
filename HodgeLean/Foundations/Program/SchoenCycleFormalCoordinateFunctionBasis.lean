import HodgeLean.Foundations.Program.SchoenCycleExactFormalCoordinateFunctions

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Supplied exact formal coordinates represented by actual functions give an actual cotangent basis with the same prescribed pullback values.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_formal_coordinate_functions_basis_with_values
    {k R A σ : Type*} [Field k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra k A] [IsLocalRing R] [IsNoetherianRing R] [Fintype σ]
    (f : R →ₐ[k] A) (q : σ → A)
    (h : ∃ (D : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃ₐ[k]
          AdicCompletion (idealOfVars σ k) (MvPolynomial σ k)) (c : σ → R),
      (∀ i, D (AdicCompletion.of _ _ (c i)) =
        AdicCompletion.of (idealOfVars σ k) (MvPolynomial σ k) (X i)) ∧
      (∀ i, f (c i) = q i)) :
    ∃ (c : σ → R) (hc : ∀ i, c i ∈ IsLocalRing.maximalIdeal R)
      (B : Module.Basis σ k (IsLocalRing.maximalIdeal R).Cotangent),
      (∀ i, B i = (IsLocalRing.maximalIdeal R).toCotangent ⟨c i, hc i⟩) ∧
      (∀ i, f (c i) = q i) := by
  obtain ⟨D, c, hD, hval⟩ := h
  obtain ⟨hc, B, hB⟩ := s2e_exact_formal_coordinate_functions D c hD
  exact ⟨c, hc, B, hB, hval⟩

#print axioms s2e_formal_coordinate_functions_basis_with_values
end HodgeLean.Foundations.Program
