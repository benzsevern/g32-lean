import HodgeLean.Foundations.Program.SchoenDegreeSubalgebraCharts
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Matching homogeneous pieces give radical control of the actual degree-subalgebra inclusion. -/
theorem s2_degreeSubalgebra_irrelevant_le_radical {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (M : ℕ) (hM : 0 < M)
    (hfull : ∀ k : ℕ, ∀ a : A, a ∈ 𝒜 (k * M) → a ∈ s2_degreeSubalgebra 𝒜 M) :
    let R := s2_degreeSubalgebra 𝒜 M
    let ℬ := s2_subringGradedPiece 𝒜 R.toSubring
    letI := s2_degreeSubalgebraGrading 𝒜 M
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      ((HomogeneousIdeal.irrelevant ℬ).toIdeal.map
        (s2_subringGradedInclusion 𝒜 R.toSubring).toRingHom).radical := by
  let R := s2_degreeSubalgebra 𝒜 M
  let ℬ := s2_subringGradedPiece 𝒜 R.toSubring
  letI : GradedRing ℬ := s2_degreeSubalgebraGrading 𝒜 M
  dsimp only
  rw [HomogeneousIdeal.irrelevant_eq_span, Ideal.span_le]
  intro a ha
  simp only [Set.mem_iUnion] at ha
  obtain ⟨n, hn, ha⟩ := ha
  have hap : a ^ M ∈ 𝒜 (n * M) := by
    have h := SetLike.pow_mem_graded M ha
    simpa only [smul_eq_mul, Nat.mul_comm M n] using h
  let b : R := ⟨a ^ M, hfull n _ hap⟩
  refine ⟨M, ?_⟩
  exact Ideal.mem_map_of_mem (s2_subringGradedInclusion 𝒜 R.toSubring).toRingHom
    (HomogeneousIdeal.mem_irrelevant_of_mem _ (Nat.mul_pos hn hM)
      (show b ∈ ℬ (n * M) from hap))

end HodgeLean.Foundations.Program
