import HodgeLean.Foundations.Program.NumeratorJetNumeratorDefs

/-! # Checks of the traced moving moments, power 11 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_11_0 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 11 0 b n = b65e_SqFormulaQ 11 0 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_11_1 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 11 1 b n = b65e_SqFormulaQ 11 1 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_11_2 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 11 2 b n = b65e_SqFormulaQ 11 2 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_11_3 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 11 3 b n = b65e_SqFormulaQ 11 3 b n.val := by
  decide +kernel

end HodgeLean.Foundations.Program
