import HodgeLean.Foundations.Program.NumeratorJetNumeratorDefs

/-! # Checks of the stored numerator jets, order 4 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_4_0_0 :
    ∀ j : Fin 10, b65e_N 4 0 j = b65e_NFormulaQ 4 0 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_4_0_1 :
    ∀ j : Fin 10, b65e_N 4 1 j = b65e_NFormulaQ 4 0 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_4_0_2 :
    ∀ j : Fin 10, b65e_N 4 2 j = b65e_NFormulaQ 4 0 2 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_4_1_0 :
    ∀ j : Fin 10, b65e_N 4 3 j = b65e_NFormulaQ 4 1 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_4_1_1 :
    ∀ j : Fin 10, b65e_N 4 4 j = b65e_NFormulaQ 4 1 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_4_1_2 :
    ∀ j : Fin 10, b65e_N 4 5 j = b65e_NFormulaQ 4 1 2 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_4_2_0 :
    ∀ j : Fin 10, b65e_N 4 6 j = b65e_NFormulaQ 4 2 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_4_2_1 :
    ∀ j : Fin 10, b65e_N 4 7 j = b65e_NFormulaQ 4 2 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_4_2_2 :
    ∀ j : Fin 10, b65e_N 4 8 j = b65e_NFormulaQ 4 2 2 j.val := by
  decide +kernel

end HodgeLean.Foundations.Program
