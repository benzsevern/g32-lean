import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Tactic.Linarith

/-! Convex carriers between affine endpoint functions over a convex base. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_convex_affine_band {E : Type*}
    [AddCommGroup E] [Module ℝ E] (C : Set E) (hC : Convex ℝ C)
    (l u : E →ᵃ[ℝ] ℝ) :
    Convex ℝ {p : E × ℝ | p.1 ∈ C ∧ l p.1 ≤ p.2 ∧ p.2 ≤ u p.1} := by
  intro x hx y hy a b ha hb hab
  refine ⟨hC hx.1 hy.1 ha hb hab, ?_, ?_⟩
  · change l (a • x.1 + b • y.1) ≤ a * x.2 + b * y.2
    rw [Convex.combo_affine_apply hab]
    exact add_le_add (mul_le_mul_of_nonneg_left hx.2.1 ha)
      (mul_le_mul_of_nonneg_left hy.2.1 hb)
  · change a * x.2 + b * y.2 ≤ u (a • x.1 + b • y.1)
    rw [Convex.combo_affine_apply hab]
    exact add_le_add (mul_le_mul_of_nonneg_left hx.2.2 ha)
      (mul_le_mul_of_nonneg_left hy.2.2 hb)

end HodgeLean.Foundations.Program
