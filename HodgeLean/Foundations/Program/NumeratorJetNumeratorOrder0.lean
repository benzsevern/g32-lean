import HodgeLean.Foundations.Program.NumeratorJetNumeratorDefs

/-! # Checks of the stored numerator jets, order 0 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_0_0_0 :
    ∀ j : Fin 10, b65e_N 0 0 j = b65e_NFormulaQ 0 0 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_0_0_1 :
    ∀ j : Fin 10, b65e_N 0 1 j = b65e_NFormulaQ 0 0 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_0_0_2 :
    ∀ j : Fin 10, b65e_N 0 2 j = b65e_NFormulaQ 0 0 2 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_0_1_0 :
    ∀ j : Fin 10, b65e_N 0 3 j = b65e_NFormulaQ 0 1 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_0_1_1 :
    ∀ j : Fin 10, b65e_N 0 4 j = b65e_NFormulaQ 0 1 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_0_1_2 :
    ∀ j : Fin 10, b65e_N 0 5 j = b65e_NFormulaQ 0 1 2 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_0_2_0 :
    ∀ j : Fin 10, b65e_N 0 6 j = b65e_NFormulaQ 0 2 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_0_2_1 :
    ∀ j : Fin 10, b65e_N 0 7 j = b65e_NFormulaQ 0 2 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_0_2_2 :
    ∀ j : Fin 10, b65e_N 0 8 j = b65e_NFormulaQ 0 2 2 j.val := by
  decide +kernel

end HodgeLean.Foundations.Program
