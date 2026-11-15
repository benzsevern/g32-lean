import HodgeLean.Foundations.Program.NumeratorJetNumeratorDefs

/-! # Checks of the polynomial parts of `D_θ q`, coefficient 4 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored polynomial-part coefficients satisfy their formula. -/
theorem b65e_G_table_4_0 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_GQ 4 0 b n = b65e_GFormulaQ 4 0 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored polynomial-part coefficients satisfy their formula. -/
theorem b65e_G_table_4_1 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_GQ 4 1 b n = b65e_GFormulaQ 4 1 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored polynomial-part coefficients satisfy their formula. -/
theorem b65e_G_table_4_2 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_GQ 4 2 b n = b65e_GFormulaQ 4 2 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored polynomial-part coefficients satisfy their formula. -/
theorem b65e_G_table_4_3 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_GQ 4 3 b n = b65e_GFormulaQ 4 3 b n.val := by
  decide +kernel

end HodgeLean.Foundations.Program
