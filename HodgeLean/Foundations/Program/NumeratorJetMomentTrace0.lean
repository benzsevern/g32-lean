import HodgeLean.Foundations.Program.NumeratorJetNumeratorDefs

/-! # Checks of the traced moving moments, power 0 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_0_0 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 0 0 b n = b65e_SqFormulaQ 0 0 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_0_1 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 0 1 b n = b65e_SqFormulaQ 0 1 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_0_2 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 0 2 b n = b65e_SqFormulaQ 0 2 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_0_3 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 0 3 b n = b65e_SqFormulaQ 0 3 b n.val := by
  decide +kernel

end HodgeLean.Foundations.Program
