import HodgeLean.Foundations.Program.SchoenIntegralClosedProjPresentation
import HodgeLean.Foundations.Program.SchoenEquivariantGenericImage
import HodgeLean.Foundations.Program.SchoenHomogeneousQuotientProjAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An integral equivariant closed Proj subscheme has its actual equivariant homogeneous coordinate quotient presentation. -/
theorem s2_equivariantClosedProj_presentation {A G : Type} [CommRing A]
    [Group G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (X : Scheme.{0}) [IsIntegral X] (ρ : G →* Aut X)
    (f : X ⟶ Proj 𝒜) [IsClosedImmersion f]
    (he : ∀ g : G, (ρ g).asIso.hom ≫ f = f ≫ (s2_projAction 𝒜 hgrade g).asIso.hom) :
    let p := f (genericPoint X)
    let I := p.asHomogeneousIdeal
    let hI := s2_fixedProjPoint_ideal_invariant 𝒜 hgrade p
      (s2_equivariantProj_genericImage_fixed 𝒜 hgrade X ρ f he)
    letI := s2_homogeneousQuotientGrading 𝒜 I
    letI := s2_quotientRingAction I.toIdeal hI
    ∃ e : X ≅ Proj (s2_homogeneousQuotientPiece 𝒜 I),
      e.hom ≫ s2_homogeneousQuotientProjMap 𝒜 I = f ∧
      ∀ g : G, (ρ g).asIso.hom ≫ e.hom = e.hom ≫
        (s2_projAction (s2_homogeneousQuotientPiece 𝒜 I)
          (s2_homogeneousQuotientAction_preserves_grading 𝒜 hgrade I hI) g).asIso.hom := by
  let p := f (genericPoint X)
  let I := p.asHomogeneousIdeal
  have hI : ∀ g : G, ∀ a ∈ I.toIdeal, g • a ∈ I.toIdeal :=
    s2_fixedProjPoint_ideal_invariant 𝒜 hgrade p
      (s2_equivariantProj_genericImage_fixed 𝒜 hgrade X ρ f he)
  letI := s2_homogeneousQuotientGrading 𝒜 I
  letI := s2_quotientRingAction I.toIdeal hI
  obtain ⟨e, hfac⟩ := s2_integralClosedProj_presentation 𝒜 X f
  haveI := s2_homogeneousQuotientProjMap_isClosedImmersion 𝒜 I
  refine ⟨e, hfac, ?_⟩
  intro g
  apply (cancel_mono (s2_homogeneousQuotientProjMap 𝒜 I)).mp
  rw [Category.assoc, hfac, Category.assoc, s2_homogeneousQuotientProjMap_equivariant,
    ← Category.assoc, hfac, he]

end HodgeLean.Foundations.Program
