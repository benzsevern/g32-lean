import HodgeLean.Foundations.Program.SchoenHomogeneousQuotientProj
import HodgeLean.Foundations.Program.SchoenHomogeneousQuotientZeroMap
import HodgeLean.Foundations.Program.SchoenProjMapBase

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual homogeneous coordinate quotient Proj map preserves its degree-zero coefficient map. -/
theorem s2_homogeneousQuotientProjMap_toSpecZero {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (I : HomogeneousIdeal 𝒜) :
    letI := s2_homogeneousQuotientGrading 𝒜 I
    s2_homogeneousQuotientProjMap 𝒜 I ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero (s2_homogeneousQuotientPiece 𝒜 I) ≫
        Spec.map (CommRingCat.ofHom (s2_homogeneousQuotientZeroMap 𝒜 I)) := by
  letI := s2_homogeneousQuotientGrading 𝒜 I
  exact s2_projMap_toSpecZero 𝒜 (s2_homogeneousQuotientPiece 𝒜 I)
    (s2_homogeneousQuotientMap 𝒜 I) _ (s2_homogeneousQuotientZeroMap 𝒜 I) (fun _ => rfl)

end HodgeLean.Foundations.Program
