import HodgeLean.Foundations.Program.SchoenHomogeneousAdjoin

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Powers of a homogeneous family are homogeneous in their actual multiplied degrees. -/
theorem s2_generatorPowers_homogeneous {A ι : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (v : ι → A)
    (hhom : ∀ i, ∃ d : ℕ, 0 < d ∧ v i ∈ 𝒜 d) (e : ι → ℕ) :
    ∀ a ∈ Set.range (fun i => v i ^ e i), ∃ n, a ∈ 𝒜 n := by
  rintro _ ⟨i, rfl⟩
  obtain ⟨d, _, hv⟩ := hhom i
  exact ⟨e i • d, SetLike.pow_mem_graded (e i) hv⟩

/-- The actual subalgebra of generator powers has its inherited homogeneous grading. -/
def s2_powerSubalgebraGrading {A ι : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (v : ι → A)
    (hhom : ∀ i, ∃ d : ℕ, 0 < d ∧ v i ∈ 𝒜 d) (e : ι → ℕ) :
    GradedRing (s2_subringGradedPiece 𝒜
      (Algebra.adjoin (𝒜 0) (Set.range fun i => v i ^ e i)).toSubring) :=
  s2_homogeneousAdjoinGrading 𝒜 _ (s2_generatorPowers_homogeneous 𝒜 v hhom e)

end HodgeLean.Foundations.Program
