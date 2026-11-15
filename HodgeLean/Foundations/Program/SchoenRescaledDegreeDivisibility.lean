import HodgeLean.Foundations.Program.SchoenRescaledProjections

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A nonzero homogeneous element has degree divisible by every scale supporting a grading. -/
theorem s2_rescaled_degree_dvd_of_ne_zero {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ)
    [GradedRing (fun n => 𝒜 (D * n))] {n : ℕ} {a : A}
    (ha : a ∈ 𝒜 n) (hane : a ≠ 0) : D ∣ n := by
  by_contra hn
  have hp := DFunLike.congr_fun (s2_rescaled_outside_projection 𝒜 D n hn) a
  change (DirectSum.decompose 𝒜 a n : A) = 0 at hp
  rw [DirectSum.decompose_of_mem_same 𝒜 ha] at hp
  exact hane hp

end HodgeLean.Foundations.Program
