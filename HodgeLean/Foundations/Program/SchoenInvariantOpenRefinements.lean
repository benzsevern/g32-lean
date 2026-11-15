import HodgeLean.Foundations.Program.SchoenQuotientOverlapNeighborhoods
import HodgeLean.Foundations.Program.SchoenInvariantAffineNeighborhoods

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Invariant principal opens refine any invariant open in an affine scheme. -/
theorem s2_invariantOpen_principal_refinement (X : Scheme.{0}) [IsAffine X]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (V : X.Opens) (hV : ∀ g : G, (ρ g).asIso.hom ⁻¹ᵁ V = V) (x : X) (hx : x ∈ V) :
    letI := s2_schemeSectionAction X G ρ
    ∃ r : FixedPoints.subring Γ(X, ⊤) G,
      x ∈ X.basicOpen (r : Γ(X, ⊤)) ∧ X.basicOpen (r : Γ(X, ⊤)) ≤ V := by
  letI := s2_schemeSectionAction X G ρ
  obtain ⟨r, hr, hsub⟩ := s2_equivariantOpenImmersion_principal_refinement G
    (s2_invariantOpenAction G ρ V hV) ρ V.ι (fun g => by
      change V.ι ≫ (ρ g).asIso.hom =
        s2_invariantOpenMap V (ρ g).asIso.hom (hV g).ge ≫ V.ι
      exact (s2_invariantOpenMap_ι V (ρ g).asIso.hom (hV g).ge).symm) ⟨x, hx⟩
  refine ⟨r, hr, ?_⟩
  intro y hy
  obtain ⟨v, rfl⟩ := hsub hy
  exact v.property

/-- An invariant morphism has invariant principal neighborhoods mapping into
any chosen open neighborhood of its image point. -/
theorem s2_invariantMap_principal_refinement (X : Scheme.{0}) [IsAffine X]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    {T : Scheme.{0}} (f : X ⟶ T) (hf : ∀ g : G, (ρ g).asIso.hom ≫ f = f)
    (V : T.Opens) (x : X) (hx : f x ∈ V) :
    letI := s2_schemeSectionAction X G ρ
    ∃ r : FixedPoints.subring Γ(X, ⊤) G,
      x ∈ X.basicOpen (r : Γ(X, ⊤)) ∧ X.basicOpen (r : Γ(X, ⊤)) ≤ f ⁻¹ᵁ V := by
  apply s2_invariantOpen_principal_refinement X G ρ (f ⁻¹ᵁ V) _ x hx
  intro g
  change ((ρ g).asIso.hom ≫ f) ⁻¹ᵁ V = f ⁻¹ᵁ V
  rw [hf g]

end HodgeLean.Foundations.Program
