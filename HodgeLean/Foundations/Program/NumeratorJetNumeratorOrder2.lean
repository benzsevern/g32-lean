import HodgeLean.Foundations.Program.NumeratorJetNumeratorDefs

/-! # Checks of the stored numerator jets, order 2 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_2_0_0 :
    ∀ j : Fin 10, b65e_N 2 0 j = b65e_NFormulaQ 2 0 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_2_0_1 :
    ∀ j : Fin 10, b65e_N 2 1 j = b65e_NFormulaQ 2 0 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_2_0_2 :
    ∀ j : Fin 10, b65e_N 2 2 j = b65e_NFormulaQ 2 0 2 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_2_1_0 :
    ∀ j : Fin 10, b65e_N 2 3 j = b65e_NFormulaQ 2 1 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_2_1_1 :
    ∀ j : Fin 10, b65e_N 2 4 j = b65e_NFormulaQ 2 1 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_2_1_2 :
    ∀ j : Fin 10, b65e_N 2 5 j = b65e_NFormulaQ 2 1 2 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_2_2_0 :
    ∀ j : Fin 10, b65e_N 2 6 j = b65e_NFormulaQ 2 2 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_2_2_1 :
    ∀ j : Fin 10, b65e_N 2 7 j = b65e_NFormulaQ 2 2 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_2_2_2 :
    ∀ j : Fin 10, b65e_N 2 8 j = b65e_NFormulaQ 2 2 2 j.val := by
  decide +kernel

end HodgeLean.Foundations.Program
