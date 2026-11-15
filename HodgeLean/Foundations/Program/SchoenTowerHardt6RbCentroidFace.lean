import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFaceWeights
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSupportedHull
import Mathlib.LinearAlgebra.AffineSpace.Centroid

/-! A simplex face contains a centroid exactly when it contains its vertex support. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_centroid_mem_face_iff {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (v : ι → E) (hv : AffineIndependent ℝ v)
    (T U : Finset ι) (hT : T.Nonempty) :
    T.centroid ℝ v ∈ convexHull ℝ (v '' (↑U : Set ι)) ↔ T ⊆ U := by
  classical
  have hsum := T.sum_centroidWeightsIndicator_eq_one_of_nonempty ℝ hT
  have hcent : T.centroid ℝ v = ∑ i, T.centroidWeightsIndicator ℝ i • v i := by
    rw [T.centroid_eq_affineCombination_fintype ℝ v]
    exact Finset.affineCombination_eq_linear_combination _ _ _ hsum
  constructor
  · intro hx i hi
    by_contra hnot
    have hs := s2v_hardt6rb_face_weight_support v hv U (T.centroidWeightsIndicator ℝ)
      hsum (hcent ▸ hx) i hnot
    have hcard : (T.card : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (Finset.card_pos.mpr hT)
    apply hcard
    simpa only [Finset.centroidWeightsIndicator, Set.indicator_of_mem hi,
      Finset.centroidWeights_apply, inv_eq_zero] using hs
  · intro hTU
    let w : stdSimplex ℝ ι := ⟨T.centroidWeightsIndicator ℝ, ?_, hsum⟩
    · rw [hcent]
      apply s2v_hardt6rb_supported_convexHull v w (v '' (↑U : Set ι))
      intro i hi
      have hiT : i ∈ T := by
        by_contra hn
        exact hi (by simp only [w, Finset.centroidWeightsIndicator, Set.indicator_of_notMem hn])
      exact ⟨i, hTU hiT, rfl⟩
    · intro i
      by_cases hi : i ∈ T
      · simp only [Finset.centroidWeightsIndicator, Set.indicator_of_mem hi,
          Finset.centroidWeights_apply, inv_nonneg, Nat.cast_nonneg]
      · simp only [Finset.centroidWeightsIndicator, Set.indicator_of_notMem hi, le_refl]

end HodgeLean.Foundations.Program
