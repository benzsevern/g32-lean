import HodgeLean.Foundations.Program.NumeratorJetNumeratorDefs

/-! # Checks of the traced moving moments, power 6 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_6_0 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 6 0 b n = b65e_SqFormulaQ 6 0 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_6_1 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 6 1 b n = b65e_SqFormulaQ 6 1 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_6_2 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 6 2 b n = b65e_SqFormulaQ 6 2 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored traced moving moments satisfy their formula. -/
theorem b65e_Sq_table_6_3 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_SqQ 6 3 b n = b65e_SqFormulaQ 6 3 b n.val := by
  decide +kernel

end HodgeLean.Foundations.Program
