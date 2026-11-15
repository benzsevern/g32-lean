import HodgeLean.Foundations.Program.SchoenHomogeneousQuotientGrading
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program

/-- Scalar stability of homogeneous pieces passes to the actual homogeneous coordinate quotient. -/
theorem s2_homogeneousQuotient_scalar_grading {K A : Type} [CommRing K] [CommRing A]
    [Algebra K A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hK : ∀ n, ∀ k : K, ∀ a ∈ 𝒜 n, k • a ∈ 𝒜 n) (I : HomogeneousIdeal 𝒜) :
    ∀ n, ∀ k : K, ∀ a ∈ s2_homogeneousQuotientPiece 𝒜 I n,
      k • a ∈ s2_homogeneousQuotientPiece 𝒜 I n := by
  intro n k a ha
  obtain ⟨b, hb, rfl⟩ := ha
  refine ⟨k • b, hK n k b hb, ?_⟩
  change Ideal.Quotient.mk I.toIdeal (k • b) = k • Ideal.Quotient.mk I.toIdeal b
  simp only [Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap]

end HodgeLean.Foundations.Program
