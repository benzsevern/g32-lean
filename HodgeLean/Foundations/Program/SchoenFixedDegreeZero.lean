import HodgeLean.Foundations.Program.SchoenFixedRingGrading

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A pointwise fixed degree-zero piece maps into the actual fixed ring's degree-zero piece. -/
def s2_fixedDegreeZeroHom {A G : Type} [CommRing A] [Group G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hzero : ∀ g : G, ∀ a ∈ 𝒜 0, g • a = a) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    𝒜 0 →+* s2_subringGradedPiece 𝒜 (FixedPoints.subring A G) 0 := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  exact
    { toFun := fun a => ⟨⟨a.val, fun g => hzero g a.val a.property⟩, a.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

end HodgeLean.Foundations.Program
