import HodgeLean.Foundations.Program.SchoenInvariantIrrelevant
import HodgeLean.Foundations.Program.SchoenProjRadicalMap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory
namespace HodgeLean.Foundations.Program

/-- The actual invariant graded-ring inclusion induces a morphism of Proj schemes. -/
def s2_invariantProjMap {K A G : Type} [Field K] [Infinite K]
    [CommRing A] [Algebra K A] [Group G] [Fintype G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hK : ∀ n, ∀ k : K, ∀ a ∈ 𝒜 n, k • a ∈ 𝒜 n) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    Proj 𝒜 ⟶ Proj (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  exact S2RadicalProj.map _ _ (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G))
    (s2_fixedRing_irrelevant_le_radical 𝒜 hgrade hK)

/-- The invariant Proj scheme morphism pulls a fixed basic open back to the
basic open of the same actual ring element. -/
theorem s2_invariantProjMap_preimage_basicOpen {K A G : Type} [Field K] [Infinite K]
    [CommRing A] [Algebra K A] [Group G] [Fintype G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hK : ∀ n, ∀ k : K, ∀ a ∈ 𝒜 n, k • a ∈ 𝒜 n)
    (a : FixedPoints.subring A G) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    s2_invariantProjMap 𝒜 hgrade hK ⁻¹ᵁ
      Proj.basicOpen (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) a =
      Proj.basicOpen 𝒜 a.val := rfl

end HodgeLean.Foundations.Program
