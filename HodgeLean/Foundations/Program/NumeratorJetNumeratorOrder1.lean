import HodgeLean.Foundations.Program.NumeratorJetNumeratorDefs

/-! # Checks of the stored numerator jets, order 1 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_1_0_0 :
    ∀ j : Fin 10, b65e_N 1 0 j = b65e_NFormulaQ 1 0 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_1_0_1 :
    ∀ j : Fin 10, b65e_N 1 1 j = b65e_NFormulaQ 1 0 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_1_0_2 :
    ∀ j : Fin 10, b65e_N 1 2 j = b65e_NFormulaQ 1 0 2 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_1_1_0 :
    ∀ j : Fin 10, b65e_N 1 3 j = b65e_NFormulaQ 1 1 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_1_1_1 :
    ∀ j : Fin 10, b65e_N 1 4 j = b65e_NFormulaQ 1 1 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_1_1_2 :
    ∀ j : Fin 10, b65e_N 1 5 j = b65e_NFormulaQ 1 1 2 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_1_2_0 :
    ∀ j : Fin 10, b65e_N 1 6 j = b65e_NFormulaQ 1 2 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_1_2_1 :
    ∀ j : Fin 10, b65e_N 1 7 j = b65e_NFormulaQ 1 2 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_1_2_2 :
    ∀ j : Fin 10, b65e_N 1 8 j = b65e_NFormulaQ 1 2 2 j.val := by
  decide +kernel

end HodgeLean.Foundations.Program
