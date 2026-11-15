import HodgeLean.Foundations.BundleThom.RealNormalCapHelpers
import Mathlib.Analysis.Convex.Contractible

/-! # Contraction geometry of real normal caps

HC no distance; AV milestone no distance. -/

noncomputable section
namespace HodgeLean.Foundations.BundleThom

/-- The positive coordinate-axis point is a star center for the positive cap.
Source: Hatcher, Algebraic Topology, §2.2, contraction of an open hemisphere. -/
theorem i1_realNormalCap_positive_starConvex (d : ℕ) :
    StarConvex ℝ (Fin.cons 1 (0 : Fin d → ℝ)) (i1_realNormalCap d true) := by
  intro x hx a b ha hb hab
  change Fin.tail x ≠ 0 ∨ 0 < x 0 at hx
  change Fin.tail (a • (Fin.cons 1 (0 : Fin d → ℝ) : Fin (d + 1) → ℝ) + b • x) ≠ 0 ∨
    0 < (a • (Fin.cons 1 (0 : Fin d → ℝ) : Fin (d + 1) → ℝ) + b • x) 0
  have ht : Fin.tail (a • (Fin.cons 1 (0 : Fin d → ℝ) : Fin (d + 1) → ℝ) + b • x) = b • Fin.tail x := by
    funext j
    simp [Fin.tail]
  rw [ht]
  by_cases hbe : b = 0
  · right
    have hae : a = 1 := by linarith
    simp [hbe, hae]
  · rcases hx with hx | hx
    · left
      exact smul_ne_zero hbe hx
    · right
      change 0 < a * 1 + b * x 0
      exact add_pos_of_nonneg_of_pos (by positivity) (mul_pos (lt_of_le_of_ne hb (Ne.symm hbe)) hx)

/-- The negative coordinate-axis point is a star center for the negative cap.
Source: Hatcher, Algebraic Topology, §2.2, contraction of an open hemisphere. -/
theorem i1_realNormalCap_negative_starConvex (d : ℕ) :
    StarConvex ℝ (Fin.cons (-1) (0 : Fin d → ℝ)) (i1_realNormalCap d false) := by
  intro x hx a b ha hb hab
  change Fin.tail x ≠ 0 ∨ x 0 < 0 at hx
  change Fin.tail (a • (Fin.cons (-1) (0 : Fin d → ℝ) : Fin (d + 1) → ℝ) + b • x) ≠ 0 ∨
    (a • (Fin.cons (-1) (0 : Fin d → ℝ) : Fin (d + 1) → ℝ) + b • x) 0 < 0
  have ht : Fin.tail (a • (Fin.cons (-1) (0 : Fin d → ℝ) : Fin (d + 1) → ℝ) + b • x) = b • Fin.tail x := by
    funext j
    simp [Fin.tail]
  rw [ht]
  by_cases hbe : b = 0
  · right
    have hae : a = 1 := by linarith
    simp [hbe, hae]
  · rcases hx with hx | hx
    · left
      exact smul_ne_zero hbe hx
    · right
      change a * (-1) + b * x 0 < 0
      exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos ha (by norm_num)) (mul_neg_of_pos_of_neg (lt_of_le_of_ne hb (Ne.symm hbe)) hx)

/-- Each actual real normal cap is contractible.
Source: Hatcher, Algebraic Topology, §2.2, contractibility of the hemisphere pieces. -/
theorem i1_realNormalCap_contractible (d : ℕ) (positive : Bool) :
    ContractibleSpace (i1_realNormalCap d positive) := by
  cases positive
  · apply (i1_realNormalCap_negative_starConvex d).contractibleSpace
    exact ⟨Fin.cons (-1) 0, Or.inr (by norm_num)⟩
  · apply (i1_realNormalCap_positive_starConvex d).contractibleSpace
    exact ⟨Fin.cons 1 0, Or.inr (by norm_num)⟩

end HodgeLean.Foundations.BundleThom
