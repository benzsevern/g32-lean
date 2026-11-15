import HodgeLean.Foundations.Program.NumeratorJetNumeratorDefs

/-! # Checks of the traced moving moments, power 7 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_7_0 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 7 0 b n = b65e_SqFormulaQ 7 0 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_7_1 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 7 1 b n = b65e_SqFormulaQ 7 1 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_7_2 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 7 2 b n = b65e_SqFormulaQ 7 2 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_7_3 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 7 3 b n = b65e_SqFormulaQ 7 3 b n.val := by
  decide +kernel

end HodgeLean.Foundations.Program
