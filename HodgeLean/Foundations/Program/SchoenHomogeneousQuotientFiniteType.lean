import HodgeLean.Foundations.Program.SchoenHomogeneousQuotientZeroMap
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Noetherian.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program

/-- Finite generation over homogeneous degree zero passes to the actual homogeneous coordinate quotient. -/
theorem s2_homogeneousQuotient_finiteType {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] [Algebra.FiniteType (𝒜 0) A]
    (I : HomogeneousIdeal 𝒜) :
    letI := s2_homogeneousQuotientGrading 𝒜 I
    Algebra.FiniteType (s2_homogeneousQuotientPiece 𝒜 I 0) (A ⧸ I.toIdeal) := by
  letI := s2_homogeneousQuotientGrading 𝒜 I
  rw [← RingHom.finiteType_algebraMap]
  apply RingHom.FiniteType.of_comp_finiteType (f := s2_homogeneousQuotientZeroMap 𝒜 I)
  change ((Ideal.Quotient.mk I.toIdeal).comp (algebraMap (𝒜 0) A)).FiniteType
  exact (RingHom.finiteType_algebraMap.mpr inferInstance).comp_surjective
    Ideal.Quotient.mk_surjective

/-- Noetherian homogeneous degree zero passes to the actual homogeneous coordinate quotient. -/
theorem s2_homogeneousQuotient_degreeZero_noetherian {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] [IsNoetherianRing (𝒜 0)]
    (I : HomogeneousIdeal 𝒜) :
    letI := s2_homogeneousQuotientGrading 𝒜 I
    IsNoetherianRing (s2_homogeneousQuotientPiece 𝒜 I 0) := by
  letI := s2_homogeneousQuotientGrading 𝒜 I
  exact isNoetherianRing_of_surjective (𝒜 0) (s2_homogeneousQuotientPiece 𝒜 I 0)
    (s2_homogeneousQuotientZeroMap 𝒜 I) (s2_homogeneousQuotientZeroMap_surjective 𝒜 I)

end HodgeLean.Foundations.Program
