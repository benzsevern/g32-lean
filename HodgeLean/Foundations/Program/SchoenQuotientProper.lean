import HodgeLean.Foundations.Program.SchoenQuotientSeparated

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A proper integral source has a proper glued invariant quotient over a
Noetherian affine base. -/
theorem s2_gluedQuotientStructure_proper {X S : Scheme.{0}} [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [IsAffine S] [IsLocallyNoetherian S]
    (s : X ⟶ S) [IsProper s]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hover : ∀ g : G, (ρ g).asIso.hom ≫ s = s)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val) :
    IsProper (s2_gluedQuotientStructure s G ρ hover hcover) := by
  haveI : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  haveI := s2_gluedQuotientStructure_separated s G ρ hover hcover
  haveI := s2_gluedQuotientStructure_universallyClosed s G ρ hover hcover
  haveI := s2_gluedQuotientStructure_locallyOfFiniteType s G ρ hover hcover
  exact {}

end HodgeLean.Foundations.Program
