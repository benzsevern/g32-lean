import HodgeLean.Foundations.Program.SchoenQuotientBase
import HodgeLean.Foundations.Program.SchoenProjectiveBaseIso

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Projectivity of the actual glued quotient structure transports through an isomorphism of the coefficient base. -/
theorem s2_gluedQuotientStructure_projective_baseIso {X S T : Scheme.{0}}
    [IsIntegral X] [IsAffine S] [IsAffine T]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val)
    (s : X ⟶ S) (hs : ∀ g : G, (ρ g).asIso.hom ≫ s = s)
    (c : S ⟶ T) [IsIso c]
    (ht : ∀ g : G, (ρ g).asIso.hom ≫ (s ≫ c) = s ≫ c)
    [IsProjective (s2_gluedQuotientStructure s G ρ hs hcover)] :
    IsProjective (s2_gluedQuotientStructure (s ≫ c) G ρ ht hcover) := by
  haveI := s2_gluedQuotientMap_epi X G ρ hcover
  have he : s2_gluedQuotientStructure (s ≫ c) G ρ ht hcover =
      s2_gluedQuotientStructure s G ρ hs hcover ≫ c := by
    apply (cancel_epi (s2_gluedQuotientMap X G ρ hcover)).mp
    rw [s2_gluedQuotientStructure_fac, ← Category.assoc,
      s2_gluedQuotientStructure_fac]
  rw [he]
  exact s2_projective_comp_base_iso _ c

end HodgeLean.Foundations.Program
