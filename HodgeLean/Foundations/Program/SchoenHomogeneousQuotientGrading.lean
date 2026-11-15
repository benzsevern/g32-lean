import HodgeLean.Foundations.Program.SchoenHomogeneousQuotientProjections

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped DirectSum BigOperators
namespace HodgeLean.Foundations.Program

/-- Recomposing the actual homogeneous quotient pieces is injective. -/
theorem s2_homogeneousQuotient_recompose_injective {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (I : HomogeneousIdeal 𝒜) :
    Function.Injective (DirectSum.coeAddMonoidHom (s2_homogeneousQuotientPiece 𝒜 I)) := by
  intro x y hxy
  apply DFinsupp.ext
  intro n
  apply Subtype.ext
  have h := congrArg (s2_homogeneousQuotientProjection 𝒜 I n) hxy
  rwa [s2_homogeneousQuotientProjection_recompose, s2_homogeneousQuotientProjection_recompose] at h

/-- Every actual quotient class is a finite sum of its homogeneous quotient pieces. -/
theorem s2_homogeneousQuotient_recompose_surjective {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (I : HomogeneousIdeal 𝒜) :
    Function.Surjective (DirectSum.coeAddMonoidHom (s2_homogeneousQuotientPiece 𝒜 I)) := by
  classical
  rw [← AddMonoidHom.mrange_eq_top]
  apply top_unique
  intro x _
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← DirectSum.sum_support_decompose 𝒜 a, map_sum]
  apply AddSubmonoid.sum_mem
  intro n _
  refine ⟨DirectSum.of (fun n => s2_homogeneousQuotientPiece 𝒜 I n) n
    ⟨Ideal.Quotient.mk I.toIdeal (DirectSum.decompose 𝒜 a n), ?_⟩, ?_⟩
  · exact ⟨DirectSum.decompose 𝒜 a n, (DirectSum.decompose 𝒜 a n).property, rfl⟩
  · exact DirectSum.coeAddMonoidHom_of _ _ _

/-- The actual quotient by a homogeneous ideal inherits a graded-ring structure. -/
def s2_homogeneousQuotientGrading {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (I : HomogeneousIdeal 𝒜) :
    GradedRing (s2_homogeneousQuotientPiece 𝒜 I) where
  toGradedMonoid := s2_homogeneousQuotientPiece_gradedMonoid 𝒜 I
  toDecomposition := (show DirectSum.IsInternal (s2_homogeneousQuotientPiece 𝒜 I) from
    ⟨s2_homogeneousQuotient_recompose_injective 𝒜 I,
      s2_homogeneousQuotient_recompose_surjective 𝒜 I⟩).chooseDecomposition

end HodgeLean.Foundations.Program
