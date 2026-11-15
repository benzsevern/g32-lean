import HodgeLean.Foundations.Program.SchoenGluedQuotientProjection

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual invariant spectrum of each nonempty affine chart of an integral source is integral. -/
instance s2_invariantAffineQuotientObj_isIntegral (X : Scheme.{0}) [IsIntegral X]
    (G : Type) [Group G] (ρ : G →* Aut X) (U : s2_InvariantAffineOpen X G ρ) :
    IsIntegral (s2_invariantAffineQuotientObj X G ρ U) := by
  dsimp only [s2_invariantAffineQuotientObj]
  infer_instance

/-- The invariant chart atlas makes the globally glued scheme reduced. -/
instance s2_invariantAffineGlued_isReduced (X : Scheme.{0}) [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X) :
    IsReduced (s2_invariantAffineGlued X G ρ) := by
  haveI (p : s2_invariantAffineGlued X G ρ) :
      _root_.IsReduced ((s2_invariantAffineGlued X G ρ).presheaf.stalk p) := by
    obtain ⟨U, u, rfl⟩ := s2_invariantAffineGluedι_jointly_surjective X G ρ p
    haveI : IsReduced (s2_invariantAffineQuotientObj X G ρ U) := inferInstance
    exact isReduced_of_injective ((s2_invariantAffineGluedι X G ρ U).stalkMap u).hom
      (asIso ((s2_invariantAffineGluedι X G ρ U).stalkMap u)).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _

/-- A covering invariant affine atlas gives an integral global invariant scheme. -/
theorem s2_invariantAffineGlued_isIntegral (X : Scheme.{0}) [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val) :
    IsIntegral (s2_invariantAffineGlued X G ρ) := by
  haveI : IrreducibleSpace (s2_invariantAffineGlued X G ρ) :=
    (s2_gluedQuotientMap_surjective X G ρ hcover).irreducibleSpace
      (s2_gluedQuotientMap X G ρ hcover).continuous
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- A quasi-compact source gives a quasi-compact glued invariant scheme. -/
theorem s2_invariantAffineGlued_compactSpace (X : Scheme.{0}) [IsIntegral X] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val) :
    CompactSpace (s2_invariantAffineGlued X G ρ) :=
  (s2_gluedQuotientMap_surjective X G ρ hcover).compactSpace
    (s2_gluedQuotientMap X G ρ hcover).continuous

end HodgeLean.Foundations.Program
