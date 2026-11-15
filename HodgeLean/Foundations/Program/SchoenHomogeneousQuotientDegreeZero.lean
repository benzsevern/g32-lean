import HodgeLean.Foundations.Program.SchoenHomogeneousQuotientPieces
import HodgeLean.Foundations.Program.SchoenQuotientRingAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program

/-- The induced homogeneous quotient action fixes degree zero whenever the original action fixes degree zero. -/
theorem s2_homogeneousQuotientAction_fixes_degreeZero {A G : Type} [CommRing A]
    [Group G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (I : HomogeneousIdeal 𝒜) (hI : ∀ g : G, ∀ a ∈ I.toIdeal, g • a ∈ I.toIdeal)
    (hzero : ∀ g : G, ∀ a ∈ 𝒜 0, g • a = a) :
    letI := s2_quotientRingAction I.toIdeal hI
    ∀ g : G, ∀ a ∈ s2_homogeneousQuotientPiece 𝒜 I 0, g • a = a := by
  letI := s2_quotientRingAction I.toIdeal hI
  intro g a ha
  obtain ⟨b, hb, rfl⟩ := ha
  change Ideal.Quotient.mk I.toIdeal (g • b) = Ideal.Quotient.mk I.toIdeal b
  rw [hzero g b hb]

end HodgeLean.Foundations.Program
