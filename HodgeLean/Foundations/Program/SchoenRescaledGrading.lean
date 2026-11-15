import Mathlib.RingTheory.GradedAlgebra.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Selecting the degrees divisible by a fixed integer preserves graded multiplication. -/
instance s2_rescaledPieces_gradedMonoid {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ) :
    SetLike.GradedMonoid (fun n => 𝒜 (D * n)) where
  one_mem := by simpa using SetLike.one_mem_graded 𝒜
  mul_mem i j a b ha hb := by
    simpa only [Nat.mul_add] using SetLike.mul_mem_graded ha hb

/-- Recomposing degrees selected by a positive scale is injective. -/
theorem s2_rescaledPieces_recompose_injective {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] {D : ℕ} (hD : 0 < D) :
    Function.Injective (DirectSum.coeAddMonoidHom (fun n => 𝒜 (D * n))) := by
  have hi := (DirectSum.Decomposition.isInternal 𝒜).addSubgroup_iSupIndep
  have hf : Function.Injective (fun n : ℕ => D * n) := by
    intro i j h
    exact Nat.eq_of_mul_eq_mul_left hD h
  exact (hi.comp hf).dfinsuppSumAddHom_injective

/-- Rescaled pieces span the ring when components outside the selected multiples vanish. -/
theorem s2_rescaledPieces_recompose_surjective {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ)
    (hzero : ∀ a : A, ∀ n : ℕ, ¬ D ∣ n → (DirectSum.decompose 𝒜 a n : A) = 0) :
    Function.Surjective (DirectSum.coeAddMonoidHom (fun n => 𝒜 (D * n))) := by
  classical
  rw [← AddMonoidHom.mrange_eq_top]
  apply top_unique
  intro a _
  rw [← DirectSum.sum_support_decompose 𝒜 a]
  apply AddSubmonoid.sum_mem
  intro n _
  by_cases hn : D ∣ n
  · obtain ⟨i, rfl⟩ := hn
    exact ⟨DirectSum.of (fun i => 𝒜 (D * i)) i (DirectSum.decompose 𝒜 a (D * i)),
      DirectSum.coeAddMonoidHom_of _ _ _⟩
  · rw [hzero a n hn]
    exact AddSubmonoid.zero_mem _

/-- A grading supported on multiples of a positive degree has an actual rescaled grading. -/
def s2_rescaledGrading {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ) (hD : 0 < D)
    (hzero : ∀ a : A, ∀ n : ℕ, ¬ D ∣ n → (DirectSum.decompose 𝒜 a n : A) = 0) :
    GradedRing (fun n => 𝒜 (D * n)) where
  toGradedMonoid := s2_rescaledPieces_gradedMonoid 𝒜 D
  toDecomposition := (show DirectSum.IsInternal (fun n => 𝒜 (D * n)) from
    ⟨s2_rescaledPieces_recompose_injective 𝒜 hD,
      s2_rescaledPieces_recompose_surjective 𝒜 D hzero⟩).chooseDecomposition

end HodgeLean.Foundations.Program
