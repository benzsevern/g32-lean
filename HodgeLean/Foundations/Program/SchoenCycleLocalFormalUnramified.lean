import HodgeLean.Foundations.Program.SchoenCycleFormalComparisonCotangentBasis
import HodgeLean.Foundations.Program.SchoenCycleCotangentUnramified
import Mathlib.LinearAlgebra.Basis.VectorSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open KaehlerDifferential
namespace HodgeLean.Foundations.Program

/-- A canonical formal equivalence of Noetherian local algebras with finite relative differentials gives unramifiedness, without a supplied source coordinate basis.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
EGA IV, 17.11.1; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_formallyUnramified_of_local_formal_equivalence
    (k A B : Type*) [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalHom (algebraMap A B)] [Module.Finite B Ω[B⁄A]]
    (ε : B →ₐ[k] k)
    (E : AdicCompletion (IsLocalRing.maximalIdeal A) A ≃ₐ[k]
      AdicCompletion (IsLocalRing.maximalIdeal B) B)
    (hE : ∀ a, E (AdicCompletion.of _ _ a) =
      AdicCompletion.of _ _ (algebraMap A B a)) : Algebra.FormallyUnramified A B := by
  let I := IsLocalRing.maximalIdeal A
  let σ := Module.Basis.ofVectorSpaceIndex k I.Cotangent
  let C : Module.Basis σ k I.Cotangent := Module.Basis.ofVectorSpace k I.Cotangent
  choose c hc using fun i : σ => I.toCotangent_surjective (C i)
  have hfc (i : σ) : algebraMap A B (c i).val ∈ IsLocalRing.maximalIdeal B := by
    change (c i).val ∈ (IsLocalRing.maximalIdeal B).comap (algebraMap A B)
    rw [IsLocalRing.maximalIdeal_comap]
    exact (c i).property
  obtain ⟨D, hD⟩ := s2e_formal_comparison_actual_cotangent_basis
    (fun i => algebraMap A B (c i).val) E (fun i => (c i).val)
    (fun i => (c i).property) hfc (fun i => hE (c i).val) C (fun i => (hc i).symm)
  exact s2e_formallyUnramified_of_source_cotangent_basis k A B σ ε
    (fun i => ⟨algebraMap A B (c i).val, hfc i⟩) D hD
    (fun i => ⟨(c i).val, rfl⟩)

#print axioms s2e_formallyUnramified_of_local_formal_equivalence
end HodgeLean.Foundations.Program
