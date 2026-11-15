import HodgeLean.Foundations.Program.NumeratorJetNumeratorDefs

/-! # Checks of the stored numerator jets, order 7 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_7_0_0 :
    ∀ j : Fin 10, b65e_N 7 0 j = b65e_NFormulaQ 7 0 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_7_0_1 :
    ∀ j : Fin 10, b65e_N 7 1 j = b65e_NFormulaQ 7 0 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_7_0_2 :
    ∀ j : Fin 10, b65e_N 7 2 j = b65e_NFormulaQ 7 0 2 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_7_1_0 :
    ∀ j : Fin 10, b65e_N 7 3 j = b65e_NFormulaQ 7 1 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_7_1_1 :
    ∀ j : Fin 10, b65e_N 7 4 j = b65e_NFormulaQ 7 1 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_7_1_2 :
    ∀ j : Fin 10, b65e_N 7 5 j = b65e_NFormulaQ 7 1 2 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_7_2_0 :
    ∀ j : Fin 10, b65e_N 7 6 j = b65e_NFormulaQ 7 2 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_7_2_1 :
    ∀ j : Fin 10, b65e_N 7 7 j = b65e_NFormulaQ 7 2 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_7_2_2 :
    ∀ j : Fin 10, b65e_N 7 8 j = b65e_NFormulaQ 7 2 2 j.val := by
  decide +kernel

end HodgeLean.Foundations.Program
