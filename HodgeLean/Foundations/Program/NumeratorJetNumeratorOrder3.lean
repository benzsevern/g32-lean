import HodgeLean.Foundations.Program.NumeratorJetNumeratorDefs

/-! # Checks of the stored numerator jets, order 3 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_3_0_0 :
    ∀ j : Fin 10, b65e_N 3 0 j = b65e_NFormulaQ 3 0 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_3_0_1 :
    ∀ j : Fin 10, b65e_N 3 1 j = b65e_NFormulaQ 3 0 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_3_0_2 :
    ∀ j : Fin 10, b65e_N 3 2 j = b65e_NFormulaQ 3 0 2 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_3_1_0 :
    ∀ j : Fin 10, b65e_N 3 3 j = b65e_NFormulaQ 3 1 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_3_1_1 :
    ∀ j : Fin 10, b65e_N 3 4 j = b65e_NFormulaQ 3 1 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_3_1_2 :
    ∀ j : Fin 10, b65e_N 3 5 j = b65e_NFormulaQ 3 1 2 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_3_2_0 :
    ∀ j : Fin 10, b65e_N 3 6 j = b65e_NFormulaQ 3 2 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_3_2_1 :
    ∀ j : Fin 10, b65e_N 3 7 j = b65e_NFormulaQ 3 2 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_3_2_2 :
    ∀ j : Fin 10, b65e_N 3 8 j = b65e_NFormulaQ 3 2 2 j.val := by
  decide +kernel

end HodgeLean.Foundations.Program
