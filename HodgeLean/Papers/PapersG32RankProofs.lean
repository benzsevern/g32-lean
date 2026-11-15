import HodgeLean.Papers.PapersG32RankStatements

namespace HodgeLean.Papers

open Matrix

private def papers8_rankRows : Fin 5 → Fin 9 := ![0, 1, 2, 3, 6]
private def papers8_rankCols : Fin 5 → Fin 10 := ![1, 2, 3, 4, 5]

private theorem papers8_rank_factor :
    papers8_rankLeft * papers8_rankRight = papers8_M0 := by
  set_option maxRecDepth 100000 in
  decide +kernel

private theorem papers8_rank_minor :
    papers8_M0.submatrix papers8_rankRows papers8_rankCols = papers8_rankMinor := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    rfl

private theorem papers8_rank_minor_unit : IsUnit papers8_rankMinor := by
  refine ⟨{ val := papers8_rankMinor
            inv := papers8_rankMinorInv
            val_inv := by decide +kernel
            inv_val := by decide +kernel }, rfl⟩

theorem papers_g32_rank_constant_aux : papers8_M0.rank = 5 := by
  apply Nat.le_antisymm
  · rw [← papers8_rank_factor]
    exact (Matrix.rank_mul_le_right papers8_rankLeft papers8_rankRight).trans
      (by simpa using Matrix.rank_le_card_height papers8_rankRight)
  · have hminor : papers8_rankMinor.rank = 5 := by
      simpa using Matrix.rank_of_isUnit papers8_rankMinor papers8_rank_minor_unit
    rw [← hminor, ← papers8_rank_minor]
    exact Matrix.rank_submatrix_le papers8_M0 papers8_rankRows papers8_rankCols

end HodgeLean.Papers
