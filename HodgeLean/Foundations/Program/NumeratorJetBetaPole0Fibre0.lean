import HodgeLean.Foundations.Program.NumeratorJetLeftDefs

/-! # Traced beta-weight checks at fixed pole 0, fibre 0 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored beta weights at pole 0, fibre 0, order 0 satisfy the trace formula. -/
theorem b65e_betaWeight_table_0_0_0 : ∀ v : Fin 6, ∀ i : Fin 4, ∀ n : Fin 8,
    b65e_betaWeightQ 0 0 0 v i n = b65e_betaWeightFormulaQ 0 0 0 v i n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored beta weights at pole 0, fibre 0, order 1 satisfy the trace formula. -/
theorem b65e_betaWeight_table_0_0_1 : ∀ v : Fin 6, ∀ i : Fin 4, ∀ n : Fin 8,
    b65e_betaWeightQ 0 0 1 v i n = b65e_betaWeightFormulaQ 0 0 1 v i n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored beta weights at pole 0, fibre 0, order 2 satisfy the trace formula. -/
theorem b65e_betaWeight_table_0_0_2 : ∀ v : Fin 6, ∀ i : Fin 4, ∀ n : Fin 8,
    b65e_betaWeightQ 0 0 2 v i n = b65e_betaWeightFormulaQ 0 0 2 v i n := by
  decide +kernel

end HodgeLean.Foundations.Program
