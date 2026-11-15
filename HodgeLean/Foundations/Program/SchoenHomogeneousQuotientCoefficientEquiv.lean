import HodgeLean.Foundations.Program.SchoenHomogeneousQuotientZeroMap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program

/-- The actual homogeneous quotient degree-zero coefficient ring retains an identified field of coefficients. -/
def s2_homogeneousQuotientCoefficientEquiv {A K : Type} [CommRing A] [Field K]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (I : HomogeneousIdeal 𝒜)
    [Nontrivial (A ⧸ I.toIdeal)] (e : 𝒜 0 ≃+* K) :
    letI := s2_homogeneousQuotientGrading 𝒜 I
    s2_homogeneousQuotientPiece 𝒜 I 0 ≃+* K := by
  letI := s2_homogeneousQuotientGrading 𝒜 I
  exact (RingEquiv.ofBijective (s2_homogeneousQuotientZeroMap 𝒜 I)
    (s2_homogeneousQuotientZeroMap_bijective 𝒜 I e)).symm.trans e

end HodgeLean.Foundations.Program
