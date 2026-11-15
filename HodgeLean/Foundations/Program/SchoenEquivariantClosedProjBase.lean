import HodgeLean.Foundations.Program.SchoenEquivariantClosedProjPresentation
import HodgeLean.Foundations.Program.SchoenHomogeneousQuotientProjBase

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual equivariant homogeneous coordinate quotient presentation retains an arbitrary specified coefficient base. -/
theorem s2_equivariantClosedProj_presentation_over {A G : Type} [CommRing A]
    [Group G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (X S : Scheme.{0}) [IsIntegral X] (ρ : G →* Aut X)
    (f : X ⟶ Proj 𝒜) [IsClosedImmersion f]
    (he : ∀ g : G, (ρ g).asIso.hom ≫ f = f ≫ (s2_projAction 𝒜 hgrade g).asIso.hom)
    (c : Spec (.of (𝒜 0)) ⟶ S) (s : X ⟶ S)
    (hbase : f ≫ Proj.toSpecZero 𝒜 ≫ c = s) :
    let p := f (genericPoint X)
    let I := p.asHomogeneousIdeal
    let hI := s2_fixedProjPoint_ideal_invariant 𝒜 hgrade p
      (s2_equivariantProj_genericImage_fixed 𝒜 hgrade X ρ f he)
    letI := s2_homogeneousQuotientGrading 𝒜 I
    letI := s2_quotientRingAction I.toIdeal hI
    ∃ e : X ≅ Proj (s2_homogeneousQuotientPiece 𝒜 I),
      e.hom ≫ s2_homogeneousQuotientProjMap 𝒜 I = f ∧
      e.hom ≫ Proj.toSpecZero (s2_homogeneousQuotientPiece 𝒜 I) ≫
        Spec.map (CommRingCat.ofHom (s2_homogeneousQuotientZeroMap 𝒜 I)) ≫ c = s ∧
      ∀ g : G, (ρ g).asIso.hom ≫ e.hom = e.hom ≫
        (s2_projAction (s2_homogeneousQuotientPiece 𝒜 I)
          (s2_homogeneousQuotientAction_preserves_grading 𝒜 hgrade I hI) g).asIso.hom := by
  let p : ProjectiveSpectrum 𝒜 := f (genericPoint X)
  let I := p.asHomogeneousIdeal
  letI := s2_homogeneousQuotientGrading 𝒜 I
  dsimp only
  obtain ⟨e, hf, heq⟩ := s2_equivariantClosedProj_presentation 𝒜 hgrade X ρ f he
  refine ⟨e, hf, ?_, heq⟩
  calc
    _ = (e.hom ≫ s2_homogeneousQuotientProjMap 𝒜 I) ≫ Proj.toSpecZero 𝒜 ≫ c := by
      rw [Category.assoc, ← Category.assoc (s2_homogeneousQuotientProjMap 𝒜 I),
        s2_homogeneousQuotientProjMap_toSpecZero, Category.assoc]
    _ = s := by rw [hf]; exact hbase

end HodgeLean.Foundations.Program
