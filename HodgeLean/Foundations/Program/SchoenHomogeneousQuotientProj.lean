import HodgeLean.Foundations.Program.SchoenHomogeneousQuotientMap
import HodgeLean.Foundations.Program.TorusAlgebraizationB54Immersion

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual quotient by a homogeneous ideal induces a morphism of Proj schemes. -/
def s2_homogeneousQuotientProjMap {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (I : HomogeneousIdeal 𝒜) :
    letI := s2_homogeneousQuotientGrading 𝒜 I
    Proj (s2_homogeneousQuotientPiece 𝒜 I) ⟶ Proj 𝒜 := by
  letI := s2_homogeneousQuotientGrading 𝒜 I
  exact Proj.map (s2_homogeneousQuotientMap 𝒜 I)
    (b54_irrelevant_le_map_of_surjective (s2_homogeneousQuotientMap 𝒜 I)
      (Ideal.Quotient.mk_surjective))

/-- The actual Proj morphism of a homogeneous ideal quotient is a scheme closed immersion. -/
theorem s2_homogeneousQuotientProjMap_isClosedImmersion {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (I : HomogeneousIdeal 𝒜) :
    letI := s2_homogeneousQuotientGrading 𝒜 I
    IsClosedImmersion (s2_homogeneousQuotientProjMap 𝒜 I) := by
  letI := s2_homogeneousQuotientGrading 𝒜 I
  exact b54_proj_map_isClosedImmersion (s2_homogeneousQuotientMap 𝒜 I) _
    (Ideal.Quotient.mk_surjective)

end HodgeLean.Foundations.Program
