import HodgeLean.Foundations.Program.NumeratorJetFixedContractions

/-! # Higher-order fixed-pole contraction checks -/

noncomputable section
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- Stored order-three entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_2_0_0_0 :
    b65e_fixedContractionQ 2 0 0 0 = 3 * b65e_fixedJet 3 0 0 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-seven entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_6_0_0_0 :
    b65e_fixedContractionQ 6 0 0 0 = 7 * b65e_fixedJet 7 0 0 0 := by
  decide +kernel

end HodgeLean.Foundations.Program
