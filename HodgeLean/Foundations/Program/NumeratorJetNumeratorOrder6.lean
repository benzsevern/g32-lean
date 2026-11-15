import HodgeLean.Foundations.Program.NumeratorJetNumeratorDefs

/-! # Checks of the stored numerator jets, order 6 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_6_0_0 :
    ∀ j : Fin 10, b65e_N 6 0 j = b65e_NFormulaQ 6 0 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_6_0_1 :
    ∀ j : Fin 10, b65e_N 6 1 j = b65e_NFormulaQ 6 0 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_6_0_2 :
    ∀ j : Fin 10, b65e_N 6 2 j = b65e_NFormulaQ 6 0 2 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_6_1_0 :
    ∀ j : Fin 10, b65e_N 6 3 j = b65e_NFormulaQ 6 1 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_6_1_1 :
    ∀ j : Fin 10, b65e_N 6 4 j = b65e_NFormulaQ 6 1 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_6_1_2 :
    ∀ j : Fin 10, b65e_N 6 5 j = b65e_NFormulaQ 6 1 2 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_6_2_0 :
    ∀ j : Fin 10, b65e_N 6 6 j = b65e_NFormulaQ 6 2 0 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_6_2_1 :
    ∀ j : Fin 10, b65e_N 6 7 j = b65e_NFormulaQ 6 2 1 j.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored numerator jets satisfy the product formula. -/
theorem b65e_N_table_6_2_2 :
    ∀ j : Fin 10, b65e_N 6 8 j = b65e_NFormulaQ 6 2 2 j.val := by
  decide +kernel

end HodgeLean.Foundations.Program
