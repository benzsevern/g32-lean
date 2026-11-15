import HodgeLean.Foundations.Program.SchoenQuotientRingAction
import HodgeLean.Foundations.Program.SchoenGradedActionHom
import HodgeLean.Foundations.Program.SchoenHomogeneousQuotientMap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A grading-preserving ring action preserves the actual homogeneous pieces of its invariant ideal quotient. -/
theorem s2_homogeneousQuotientAction_preserves_grading {A G : Type} [CommRing A]
    [Group G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (I : HomogeneousIdeal 𝒜) (hI : ∀ g : G, ∀ a ∈ I.toIdeal, g • a ∈ I.toIdeal) :
    letI := s2_quotientRingAction I.toIdeal hI
    ∀ g : G, ∀ n, ∀ a ∈ s2_homogeneousQuotientPiece 𝒜 I n,
      g • a ∈ s2_homogeneousQuotientPiece 𝒜 I n := by
  letI := s2_quotientRingAction I.toIdeal hI
  intro g n a ha
  obtain ⟨b, hb, rfl⟩ := ha
  exact ⟨g • b, hgrade g n b hb, rfl⟩

/-- The actual graded quotient map intertwines the original and induced ring actions. -/
theorem s2_homogeneousQuotientMap_action_commutes {A G : Type} [CommRing A]
    [Group G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (I : HomogeneousIdeal 𝒜) (hI : ∀ g : G, ∀ a ∈ I.toIdeal, g • a ∈ I.toIdeal) (g : G) :
    letI := s2_homogeneousQuotientGrading 𝒜 I
    letI := s2_quotientRingAction I.toIdeal hI
    (s2_homogeneousQuotientMap 𝒜 I).comp (s2_gradedActionHom 𝒜 hgrade g) =
      (s2_gradedActionHom (s2_homogeneousQuotientPiece 𝒜 I)
        (s2_homogeneousQuotientAction_preserves_grading 𝒜 hgrade I hI) g).comp
          (s2_homogeneousQuotientMap 𝒜 I) := by
  letI := s2_homogeneousQuotientGrading 𝒜 I
  letI := s2_quotientRingAction I.toIdeal hI
  apply GradedRingHom.ext
  intro a
  rfl

end HodgeLean.Foundations.Program
