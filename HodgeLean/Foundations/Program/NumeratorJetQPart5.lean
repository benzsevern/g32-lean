import HodgeLean.Foundations.Program.NumeratorJetNumeratorDefs

/-! # Checks of the polynomial parts of `D_θ q`, coefficient 5 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored polynomial-part coefficients satisfy their formula. -/
theorem b65e_G_table_5_0 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_GQ 5 0 b n = b65e_GFormulaQ 5 0 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored polynomial-part coefficients satisfy their formula. -/
theorem b65e_G_table_5_1 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_GQ 5 1 b n = b65e_GFormulaQ 5 1 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored polynomial-part coefficients satisfy their formula. -/
theorem b65e_G_table_5_2 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_GQ 5 2 b n = b65e_GFormulaQ 5 2 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored polynomial-part coefficients satisfy their formula. -/
theorem b65e_G_table_5_3 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_GQ 5 3 b n = b65e_GFormulaQ 5 3 b n.val := by
  decide +kernel

end HodgeLean.Foundations.Program
