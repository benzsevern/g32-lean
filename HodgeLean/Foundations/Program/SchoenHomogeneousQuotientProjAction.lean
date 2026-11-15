import HodgeLean.Foundations.Program.SchoenHomogeneousQuotientAction
import HodgeLean.Foundations.Program.SchoenHomogeneousQuotientProj
import HodgeLean.Foundations.Program.SchoenProjAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual homogeneous quotient Proj closed immersion intertwines the original and induced scheme actions. -/
theorem s2_homogeneousQuotientProjMap_equivariant {A G : Type} [CommRing A]
    [Group G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (I : HomogeneousIdeal 𝒜) (hI : ∀ g : G, ∀ a ∈ I.toIdeal, g • a ∈ I.toIdeal) (g : G) :
    letI := s2_homogeneousQuotientGrading 𝒜 I
    letI := s2_quotientRingAction I.toIdeal hI
    (s2_projAction (s2_homogeneousQuotientPiece 𝒜 I)
      (s2_homogeneousQuotientAction_preserves_grading 𝒜 hgrade I hI) g).asIso.hom ≫
        s2_homogeneousQuotientProjMap 𝒜 I =
    s2_homogeneousQuotientProjMap 𝒜 I ≫ (s2_projAction 𝒜 hgrade g).asIso.hom := by
  letI := s2_homogeneousQuotientGrading 𝒜 I
  letI := s2_quotientRingAction I.toIdeal hI
  change Proj.map _ _ ≫ Proj.map _ _ = Proj.map _ _ ≫ Proj.map _ _
  rw [← Proj.map_comp, ← Proj.map_comp]
  congr 1

end HodgeLean.Foundations.Program
