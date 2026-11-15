import HodgeLean.Foundations.Program.NumeratorJetNumeratorDefs

/-! # Checks of the traced moving moments, power 3 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_3_0 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 3 0 b n = b65e_SqFormulaQ 3 0 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_3_1 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 3 1 b n = b65e_SqFormulaQ 3 1 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_3_2 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 3 2 b n = b65e_SqFormulaQ 3 2 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_3_3 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 3 3 b n = b65e_SqFormulaQ 3 3 b n.val := by
  decide +kernel

end HodgeLean.Foundations.Program
