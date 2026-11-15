import HodgeLean.Foundations.Program.SchoenGluedQuotientDescent
import HodgeLean.Foundations.Program.SchoenQuotientIntegrality

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The structure morphism on the glued invariant scheme induced by an invariant affine base map. -/
def s2_gluedQuotientStructure {X S : Scheme.{0}} [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [IsAffine S]
    (s : X ⟶ S) (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hover : ∀ g : G, (ρ g).asIso.hom ≫ s = s)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val) :
    s2_invariantAffineGlued X G ρ ⟶ S :=
  (s2_gluedQuotientDesc_affine X G ρ hcover S s hover).exists.choose

/-- The actual quotient projection respects its induced structure morphism. -/
theorem s2_gluedQuotientStructure_fac {X S : Scheme.{0}} [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [IsAffine S]
    (s : X ⟶ S) (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hover : ∀ g : G, (ρ g).asIso.hom ≫ s = s)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val) :
    s2_gluedQuotientMap X G ρ hcover ≫
      s2_gluedQuotientStructure s G ρ hover hcover = s :=
  (s2_gluedQuotientDesc_affine X G ρ hcover S s hover).exists.choose_spec

/-- Universal closedness descends along the surjective invariant projection. -/
theorem s2_gluedQuotientStructure_universallyClosed {X S : Scheme.{0}} [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [IsAffine S]
    (s : X ⟶ S) [UniversallyClosed s]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hover : ∀ g : G, (ρ g).asIso.hom ≫ s = s)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val) :
    UniversallyClosed (s2_gluedQuotientStructure s G ρ hover hcover) := by
  haveI : Surjective (s2_gluedQuotientMap X G ρ hcover) :=
    ⟨s2_gluedQuotientMap_surjective X G ρ hcover⟩
  haveI : UniversallyClosed (s2_gluedQuotientMap X G ρ hcover ≫
      s2_gluedQuotientStructure s G ρ hover hcover) := by
    rw [s2_gluedQuotientStructure_fac]
    infer_instance
  exact UniversallyClosed.of_comp_surjective (s2_gluedQuotientMap X G ρ hcover) _

/-- Quasi-compactness of the source structure map passes to the induced quotient structure. -/
theorem s2_gluedQuotientStructure_quasiCompact {X S : Scheme.{0}} [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [IsAffine S]
    (s : X ⟶ S) [QuasiCompact s]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hover : ∀ g : G, (ρ g).asIso.hom ≫ s = s)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val) :
    QuasiCompact (s2_gluedQuotientStructure s G ρ hover hcover) := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  haveI := s2_invariantAffineGlued_compactSpace X G ρ hcover
  infer_instance

end HodgeLean.Foundations.Program
