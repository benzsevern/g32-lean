import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidFace
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Expansion of finite centroid combinations into nonnegative original-vertex weights. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_centroid_mixture_weights {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]
    (v : ι → E) (C : Finset (Finset ι)) (hne : ∀ T ∈ C, T.Nonempty)
    (a : Finset ι → ℝ) (ha : ∀ T ∈ C, 0 ≤ a T) (hasum : (∑ T ∈ C, a T) = 1) :
    let b : ι → ℝ := fun i => ∑ T ∈ C, if i ∈ T then a T * (T.card : ℝ)⁻¹ else 0
    (∀ i, 0 ≤ b i) ∧ (∑ i, b i) = 1 ∧
      (∑ i, b i • v i) = ∑ T ∈ C, a T • T.centroid ℝ v := by
  classical
  intro b
  have hprod (T : Finset ι) (i : ι) :
      (if i ∈ T then a T * (T.card : ℝ)⁻¹ else 0) = a T * T.centroidWeightsIndicator ℝ i := by
    by_cases hi : i ∈ T
    · simp only [hi, ite_true, Finset.centroidWeightsIndicator,
        Set.indicator_of_mem hi, Finset.centroidWeights_apply]
    · simp only [hi, ite_false, Finset.centroidWeightsIndicator,
        Set.indicator_of_notMem hi, mul_zero]
  have hcent (T : Finset ι) (hT : T ∈ C) :
      T.centroid ℝ v = ∑ i, T.centroidWeightsIndicator ℝ i • v i := by
    rw [T.centroid_eq_affineCombination_fintype ℝ v]
    exact Finset.affineCombination_eq_linear_combination _ _ _
      (T.sum_centroidWeightsIndicator_eq_one_of_nonempty ℝ (hne T hT))
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Finset.sum_nonneg
    intro T hT
    split_ifs
    · exact mul_nonneg (ha T hT) (inv_nonneg.mpr (Nat.cast_nonneg _))
    · exact le_rfl
  · change (∑ i, ∑ T ∈ C, if i ∈ T then a T * (T.card : ℝ)⁻¹ else 0) = 1
    simp_rw [hprod]
    rw [Finset.sum_comm]
    calc
      (∑ T ∈ C, ∑ i, a T * T.centroidWeightsIndicator ℝ i) = ∑ T ∈ C, a T := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [← Finset.mul_sum, T.sum_centroidWeightsIndicator_eq_one_of_nonempty ℝ (hne T hT), mul_one]
      _ = 1 := hasum
  · change (∑ i, (∑ T ∈ C, if i ∈ T then a T * (T.card : ℝ)⁻¹ else 0) • v i) = _
    simp_rw [hprod, Finset.sum_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro T hT
    rw [hcent T hT]
    simp only [Finset.smul_sum, smul_smul]

end HodgeLean.Foundations.Program
