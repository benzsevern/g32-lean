import HodgeLean.Foundations.Program.SchoenRescaledProjections
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Positive degree rescaling preserves exactly the actual homogeneous ideals. -/
theorem s2_rescaled_isHomogeneous_iff {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ) (hD : 0 < D)
    [GradedRing (fun n => 𝒜 (D * n))] (I : Ideal A) :
    I.IsHomogeneous 𝒜 ↔ I.IsHomogeneous (fun n => 𝒜 (D * n)) := by
  constructor
  · intro h n a ha
    change GradedRing.proj (fun j => 𝒜 (D * j)) n a ∈ I
    rw [← s2_rescaled_projection 𝒜 D hD n]
    exact h (D * n) ha
  · intro h n a ha
    change GradedRing.proj 𝒜 n a ∈ I
    by_cases hn : D ∣ n
    · obtain ⟨i, rfl⟩ := hn
      rw [s2_rescaled_projection 𝒜 D hD i]
      exact h i ha
    · rw [s2_rescaled_outside_projection 𝒜 D n hn]
      exact I.zero_mem

/-- Positive degree rescaling preserves the actual irrelevant ideal of the ring. -/
theorem s2_rescaled_irrelevant_eq {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ) (hD : 0 < D)
    [GradedRing (fun n => 𝒜 (D * n))] :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal =
      (HomogeneousIdeal.irrelevant (fun n => 𝒜 (D * n))).toIdeal := by
  apply Ideal.ext
  intro a
  change GradedRing.proj 𝒜 0 a = 0 ↔ GradedRing.proj (fun n => 𝒜 (D * n)) 0 a = 0
  have hp : GradedRing.proj 𝒜 0 = GradedRing.proj (fun n => 𝒜 (D * n)) 0 := by
    simpa only [Nat.mul_zero] using s2_rescaled_projection 𝒜 D hD 0
  rw [hp]

end HodgeLean.Foundations.Program
