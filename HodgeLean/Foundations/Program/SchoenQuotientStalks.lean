import HodgeLean.Foundations.Program.SchoenGluedQuotientOrbits

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Pullback along an affine invariant projection is injective on each source stalk. -/
theorem s2_affineSchemeQuotientMap_stalkMap_injective (X : Scheme.{0}) [IsAffine X]
    [IsDomain Γ(X, ⊤)] (G : Type) [Group G] (ρ : G →* Aut X) (x : X) :
    Function.Injective ((s2_affineSchemeQuotientMap X G ρ).stalkMap x) := by
  letI := s2_schemeSectionAction X G ρ
  unfold s2_affineSchemeQuotientMap
  rw [Scheme.Hom.stalkMap_comp]
  exact (asIso (X.isoSpec.hom.stalkMap x)).commRingCatIsoToRingEquiv.injective.comp
    (s2_spec_stalkMap_injective _ Γ(X, ⊤) (FixedPoints.subring Γ(X, ⊤) G).subtype
      Subtype.val_injective (X.isoSpec.hom x))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The affine chart equations make global quotient pullback injective on every source stalk. -/
theorem s2_gluedQuotientMap_stalkMap_injective (X : Scheme.{0}) [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val) (x : X) :
    Function.Injective ((s2_gluedQuotientMap X G ρ hcover).stalkMap x) := by
  obtain ⟨U, hx⟩ := hcover x
  let u : U.val.toScheme := ⟨x, hx⟩
  have hi : Function.Injective ((U.val.ι ≫ s2_gluedQuotientMap X G ρ hcover).stalkMap u) := by
    rw [s2_gluedQuotientMap_ι X G ρ hcover U, Scheme.Hom.stalkMap_comp]
    exact (s2_affineSchemeQuotientMap_stalkMap_injective U.val.toScheme G
      (s2_invariantAffineOpenAction X G ρ U) u).comp
      (asIso ((s2_invariantAffineGluedι X G ρ U).stalkMap
        (s2_invariantAffineProjection X G ρ U u))).commRingCatIsoToRingEquiv.injective
  rw [Scheme.Hom.stalkMap_comp] at hi
  intro a b hab
  apply hi
  exact congrArg (U.val.ι.stalkMap u) hab

end HodgeLean.Foundations.Program
