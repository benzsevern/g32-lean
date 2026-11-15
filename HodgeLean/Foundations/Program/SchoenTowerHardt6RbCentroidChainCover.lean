import HodgeLean.Foundations.Program.SchoenTowerHardt6RbIndicatorDecomposition
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidMixture

/-! Every finite convex combination belongs to a centroid-chain simplex with matching support. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_centroid_chain_cover {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (v : ι → E) (w : stdSimplex ℝ ι) :
    ∃ C : Finset (Finset ι), (∀ T ∈ C, T.Nonempty) ∧
      (∀ S ∈ C, ∀ T ∈ C, S ⊆ T ∨ T ⊆ S) ∧
      (∀ T ∈ C, ∀ i ∈ T, 0 < w.val i) ∧
      (∑ i, w.val i • v i) ∈ convexHull ℝ
        ((fun T => T.centroid ℝ v) '' (↑C : Set (Finset ι))) := by
  classical
  obtain ⟨C, a, hne, hchain, ha, hsupport, hrep⟩ :=
    s2v_hardt6rb_indicator_chain_decomposition w.val w.property.1
  let b : Finset ι → ℝ := fun T => (T.card : ℝ) * a T
  have hb : ∀ T ∈ C, 0 ≤ b T := fun T hT => mul_nonneg (Nat.cast_nonneg _) (ha T hT)
  have hbsum : (∑ T ∈ C, b T) = 1 := by
    calc
      (∑ T ∈ C, b T) = ∑ T ∈ C, ∑ i, if i ∈ T then a T else 0 := by
        apply Finset.sum_congr rfl
        intro T hT
        simp only [b, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      _ = ∑ i, ∑ T ∈ C, if i ∈ T then a T else 0 := Finset.sum_comm
      _ = ∑ i, w.val i := Finset.sum_congr rfl (fun i _ => (hrep i).symm)
      _ = 1 := w.property.2
  have hcancel (T : Finset ι) (hT : T ∈ C) : b T * (T.card : ℝ)⁻¹ = a T := by
    have hcard : (T.card : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (Finset.card_pos.mpr (hne T hT))
    change ((T.card : ℝ) * a T) * (T.card : ℝ)⁻¹ = a T
    rw [mul_comm (T.card : ℝ) (a T), mul_assoc, mul_inv_cancel₀ hcard, mul_one]
  have hbeta (i : ι) : (∑ T ∈ C, if i ∈ T then b T * (T.card : ℝ)⁻¹ else 0) = w.val i := by
    rw [hrep i]
    apply Finset.sum_congr rfl
    intro T hT
    rw [hcancel T hT]
  obtain ⟨_, _, hpoint⟩ := s2v_hardt6rb_centroid_mixture_weights v C hne b hb hbsum
  have hpoint' : (∑ T ∈ C, b T • T.centroid ℝ v) = ∑ i, w.val i • v i := by
    rw [← hpoint]
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun r : ℝ => r • v i) (hbeta i)
  refine ⟨C, hne, hchain, hsupport, ?_⟩
  apply mem_convexHull_of_exists_fintype (fun T : C => b T.val)
    (fun T : C => T.val.centroid ℝ v)
  · intro T
    exact hb T.val T.property
  · rw [Finset.univ_eq_attach, Finset.sum_attach C b]
    exact hbsum
  · intro T
    exact ⟨T.val, T.property, rfl⟩
  · rw [Finset.univ_eq_attach, Finset.sum_attach C (fun T => b T • T.centroid ℝ v)]
    exact hpoint'

end HodgeLean.Foundations.Program
