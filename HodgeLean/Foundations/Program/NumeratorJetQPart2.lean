import HodgeLean.Foundations.Program.NumeratorJetNumeratorDefs

/-! # Checks of the polynomial parts of `D_θ q`, coefficient 2 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored polynomial-part coefficients satisfy their formula. -/
theorem b65e_G_table_2_0 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_GQ 2 0 b n = b65e_GFormulaQ 2 0 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored polynomial-part coefficients satisfy their formula. -/
theorem b65e_G_table_2_1 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_GQ 2 1 b n = b65e_GFormulaQ 2 1 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored polynomial-part coefficients satisfy their formula. -/
theorem b65e_G_table_2_2 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_GQ 2 2 b n = b65e_GFormulaQ 2 2 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored polynomial-part coefficients satisfy their formula. -/
theorem b65e_G_table_2_3 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_GQ 2 3 b n = b65e_GFormulaQ 2 3 b n.val := by
  decide +kernel

end HodgeLean.Foundations.Program
