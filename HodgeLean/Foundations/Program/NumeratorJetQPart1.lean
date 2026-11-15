import HodgeLean.Foundations.Program.NumeratorJetNumeratorDefs

/-! # Checks of the polynomial parts of `D_θ q`, coefficient 1 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored polynomial-part coefficients satisfy their formula. -/
theorem b65e_G_table_1_0 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_GQ 1 0 b n = b65e_GFormulaQ 1 0 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored polynomial-part coefficients satisfy their formula. -/
theorem b65e_G_table_1_1 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_GQ 1 1 b n = b65e_GFormulaQ 1 1 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored polynomial-part coefficients satisfy their formula. -/
theorem b65e_G_table_1_2 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_GQ 1 2 b n = b65e_GFormulaQ 1 2 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored polynomial-part coefficients satisfy their formula. -/
theorem b65e_G_table_1_3 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_GQ 1 3 b n = b65e_GFormulaQ 1 3 b n.val := by
  decide +kernel

end HodgeLean.Foundations.Program
