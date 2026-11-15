import HodgeLean.Foundations.Program.NumeratorJetQSystemDefs

/-! # Rational checks for the beta columns of the q-system jets -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored order-0 beta columns satisfy the finite formula. -/
theorem b65e_qBetaJet_table_0 : b65e_qBetaJetQ 0 = b65e_qBetaFormulaQ 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored order-1 beta columns satisfy the finite formula. -/
theorem b65e_qBetaJet_table_1 : b65e_qBetaJetQ 1 = b65e_qBetaFormulaQ 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored order-2 beta columns satisfy the finite formula. -/
theorem b65e_qBetaJet_table_2 : b65e_qBetaJetQ 2 = b65e_qBetaFormulaQ 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored order-3 beta columns satisfy the finite formula. -/
theorem b65e_qBetaJet_table_3 : b65e_qBetaJetQ 3 = b65e_qBetaFormulaQ 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored order-4 beta columns satisfy the finite formula. -/
theorem b65e_qBetaJet_table_4 : b65e_qBetaJetQ 4 = b65e_qBetaFormulaQ 4 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored order-5 beta columns satisfy the finite formula. -/
theorem b65e_qBetaJet_table_5 : b65e_qBetaJetQ 5 = b65e_qBetaFormulaQ 5 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored order-6 beta columns satisfy the finite formula. -/
theorem b65e_qBetaJet_table_6 : b65e_qBetaJetQ 6 = b65e_qBetaFormulaQ 6 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored order-7 beta columns satisfy the finite formula. -/
theorem b65e_qBetaJet_table_7 : b65e_qBetaJetQ 7 = b65e_qBetaFormulaQ 7 := by
  decide +kernel

end HodgeLean.Foundations.Program
