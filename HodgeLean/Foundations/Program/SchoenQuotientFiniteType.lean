import HodgeLean.Foundations.Program.SchoenFiniteTypeDescent
import HodgeLean.Foundations.Program.SchoenQuotientBase

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Pullback of global sections along the actual affine invariant projection is injective. -/
theorem s2_affineSchemeQuotientMap_appTop_injective (X : Scheme.{0}) [IsAffine X]
    (G : Type) [Group G] (ρ : G →* Aut X) :
    Function.Injective (s2_affineSchemeQuotientMap X G ρ).appTop := by
  letI := s2_schemeSectionAction X G ρ
  let f := CommRingCat.ofHom (FixedPoints.subring Γ(X, ⊤) G).subtype
  have hf : Function.Injective (Spec.map f).appTop :=
    (RingHom.injective_respectsIso.arrow_mk_iso_iff (arrowIsoΓSpecOfIsAffine f)).mp
      Subtype.val_injective
  unfold s2_affineSchemeQuotientMap
  rw [Scheme.Hom.comp_appTop]
  have hi : Function.Injective X.isoSpec.hom.appTop := by
    change Function.Injective X.toSpecΓ.appTop
    rw [Scheme.toSpecΓ_appTop]
    exact (Scheme.ΓSpecIso Γ(X, ⊤)).commRingCatIsoToRingEquiv.injective
  exact hi.comp hf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The induced structure map on the glued invariant scheme is locally of finite type
for finite-type actions over a Noetherian affine base. -/
theorem s2_gluedQuotientStructure_locallyOfFiniteType {X S : Scheme.{0}} [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [IsAffine S]
    [IsNoetherianRing Γ(S, ⊤)] (s : X ⟶ S) [LocallyOfFiniteType s]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hover : ∀ g : G, (ρ g).asIso.hom ≫ s = s)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val) :
    LocallyOfFiniteType (s2_gluedQuotientStructure s G ρ hover hcover) := by
  apply IsZariskiLocalAtSource.of_openCover
    (Scheme.IsLocallyDirected.openCover (s2_invariantAffineDiagram X G ρ))
  intro U
  change LocallyOfFiniteType (s2_invariantAffineGluedι X G ρ U ≫
    s2_gluedQuotientStructure s G ρ hover hcover)
  haveI : IsAffine (s2_invariantAffineQuotientObj X G ρ U) := by
    dsimp only [s2_invariantAffineQuotientObj]
    infer_instance
  haveI : IsFinite (s2_invariantAffineProjection X G ρ U) :=
    s2_invariantAffineProjection_finite_over s G ρ hover U
  haveI : LocallyOfFiniteType (s2_invariantAffineProjection X G ρ U ≫
      (s2_invariantAffineGluedι X G ρ U ≫ s2_gluedQuotientStructure s G ρ hover hcover)) := by
    rw [← Category.assoc, ← s2_gluedQuotientMap_ι X G ρ hcover U, Category.assoc,
      s2_gluedQuotientStructure_fac]
    infer_instance
  exact s2_affine_finiteType_descent (s2_invariantAffineProjection X G ρ U) _
    (s2_affineSchemeQuotientMap_appTop_injective U.val.toScheme G
      (s2_invariantAffineOpenAction X G ρ U))

end HodgeLean.Foundations.Program
