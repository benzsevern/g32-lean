import HodgeLean.Foundations.Program.NumeratorJetNumeratorDefs

/-! # Checks of the traced moving moments, power 5 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_5_0 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 5 0 b n = b65e_SqFormulaQ 5 0 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_5_1 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 5 1 b n = b65e_SqFormulaQ 5 1 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_5_2 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 5 2 b n = b65e_SqFormulaQ 5 2 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_5_3 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 5 3 b n = b65e_SqFormulaQ 5 3 b n.val := by
  decide +kernel

end HodgeLean.Foundations.Program
