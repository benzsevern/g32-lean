import HodgeLean.Foundations.Program.SchoenFixedDegreeZero

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Taking invariants preserves a pointwise fixed degree-zero ring by its actual inclusion. -/
def s2_fixedDegreeZeroEquiv {A G : Type} [CommRing A] [Group G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hzero : ∀ g : G, ∀ a ∈ 𝒜 0, g • a = a) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    𝒜 0 ≃+* s2_subringGradedPiece 𝒜 (FixedPoints.subring A G) 0 := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  exact
    { s2_fixedDegreeZeroHom 𝒜 hgrade hzero with
      invFun := fun a => ⟨a.val.val, a.property⟩
      left_inv := fun a => rfl
      right_inv := fun a => rfl }

end HodgeLean.Foundations.Program
