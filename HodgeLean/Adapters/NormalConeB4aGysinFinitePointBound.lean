import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Max

noncomputable section
namespace HodgeLean.Adapters

/-- A nonzero simultaneous coordinate vector bounds its scalar eigenvalue
by the sum of the norms of the matrix coefficients. -/
theorem a3b4a_gysin_coordinate_eigenvalue_bound
    {I : Type*} [Fintype I] (x : I → ℂ) (hx : x ≠ 0)
    (a : I → I → ℂ) (z : ℂ)
    (heq : ∀ i, z * x i = ∑ j, a i j * x j) :
    ‖z‖ ≤ ∑ i, ∑ j, ‖a i j‖ := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
    by_contra h
    apply hx
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset I)
    (fun j => ‖x j‖) ⟨k, Finset.mem_univ k⟩
  have hi : 0 < ‖x i‖ := lt_of_lt_of_le (norm_pos_iff.mpr hk) (hmax k (Finset.mem_univ k))
  apply (mul_le_mul_iff_left₀ hi).mp
  calc
    ‖z‖ * ‖x i‖ = ‖z * x i‖ := (norm_mul _ _).symm
    _ = ‖∑ j, a i j * x j‖ := congrArg norm (heq i)
    _ ≤ ∑ j, ‖a i j * x j‖ := norm_sum_le _ _
    _ = ∑ j, ‖a i j‖ * ‖x j‖ := Finset.sum_congr rfl fun j _ => norm_mul _ _
    _ ≤ ∑ j, ‖a i j‖ * ‖x i‖ := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hmax j (Finset.mem_univ j)) (norm_nonneg _)
    _ = (∑ j, ‖a i j‖) * ‖x i‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ i, ∑ j, ‖a i j‖) * ‖x i‖ := mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun k _ => norm_nonneg (a j k))
        (Finset.mem_univ i)) (norm_nonneg _)

end HodgeLean.Adapters
