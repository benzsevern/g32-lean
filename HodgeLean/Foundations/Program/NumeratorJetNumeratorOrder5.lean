import HodgeLean.Foundations.Program.NumeratorJetNumeratorDefs

/-! # Checks of the stored numerator jets, order 5 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_5_0_0 :
    ∀ j : Fin 10, b65e_N 5 0 j = b65e_NFormulaQ 5 0 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_5_0_1 :
    ∀ j : Fin 10, b65e_N 5 1 j = b65e_NFormulaQ 5 0 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_5_0_2 :
    ∀ j : Fin 10, b65e_N 5 2 j = b65e_NFormulaQ 5 0 2 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_5_1_0 :
    ∀ j : Fin 10, b65e_N 5 3 j = b65e_NFormulaQ 5 1 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_5_1_1 :
    ∀ j : Fin 10, b65e_N 5 4 j = b65e_NFormulaQ 5 1 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_5_1_2 :
    ∀ j : Fin 10, b65e_N 5 5 j = b65e_NFormulaQ 5 1 2 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_5_2_0 :
    ∀ j : Fin 10, b65e_N 5 6 j = b65e_NFormulaQ 5 2 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_5_2_1 :
    ∀ j : Fin 10, b65e_N 5 7 j = b65e_NFormulaQ 5 2 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_5_2_2 :
    ∀ j : Fin 10, b65e_N 5 8 j = b65e_NFormulaQ 5 2 2 j.val := by
  decide +kernel

end HodgeLean.Foundations.Program
