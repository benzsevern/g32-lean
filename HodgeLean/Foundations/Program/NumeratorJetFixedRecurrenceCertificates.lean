import HodgeLean.Foundations.Program.NumeratorJetFixedHigherCertificates
import HodgeLean.Foundations.Program.NumeratorJetFixedOrder3Pole0
import HodgeLean.Foundations.Program.NumeratorJetFixedOrder3Pole1
import HodgeLean.Foundations.Program.NumeratorJetFixedOrder3Pole2
import HodgeLean.Foundations.Program.NumeratorJetFixedOrder3Pole3
import HodgeLean.Foundations.Program.NumeratorJetFixedOrder4Pole0
import HodgeLean.Foundations.Program.NumeratorJetFixedOrder4Pole1
import HodgeLean.Foundations.Program.NumeratorJetFixedOrder4Pole2
import HodgeLean.Foundations.Program.NumeratorJetFixedOrder4Pole3
import HodgeLean.Foundations.Program.NumeratorJetFixedOrder5Pole0
import HodgeLean.Foundations.Program.NumeratorJetFixedOrder5Pole1
import HodgeLean.Foundations.Program.NumeratorJetFixedOrder5Pole2
import HodgeLean.Foundations.Program.NumeratorJetFixedOrder5Pole3
import HodgeLean.Foundations.Program.NumeratorJetFixedOrder6Pole0
import HodgeLean.Foundations.Program.NumeratorJetFixedOrder6Pole1
import HodgeLean.Foundations.Program.NumeratorJetFixedOrder6Pole2
import HodgeLean.Foundations.Program.NumeratorJetFixedOrder6Pole3
import HodgeLean.Foundations.Program.NumeratorJetFixedOrder7Pole0
import HodgeLean.Foundations.Program.NumeratorJetFixedOrder7Pole1
import HodgeLean.Foundations.Program.NumeratorJetFixedOrder7Pole2
import HodgeLean.Foundations.Program.NumeratorJetFixedOrder7Pole3

/-! # Rational fixed-pole recurrence certificates for all stored higher orders -/

noncomputable section
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- Every stored order-2 fixed-residue entry satisfies its rational contraction. -/
theorem b65e_fixedContraction_table_order2 (k i j : Fin 4) :
    b65e_fixedContractionQ 1 k i j = 2 * b65e_fixedJet 2 k i j := by
  fin_cases k <;> fin_cases i <;> fin_cases j
  · exact b65e_fixedContraction_table_1_0_0_0
  · exact b65e_fixedContraction_table_1_0_0_1
  · exact b65e_fixedContraction_table_1_0_0_2
  · exact b65e_fixedContraction_table_1_0_0_3
  · exact b65e_fixedContraction_table_1_0_1_0
  · exact b65e_fixedContraction_table_1_0_1_1
  · exact b65e_fixedContraction_table_1_0_1_2
  · exact b65e_fixedContraction_table_1_0_1_3
  · exact b65e_fixedContraction_table_1_0_2_0
  · exact b65e_fixedContraction_table_1_0_2_1
  · exact b65e_fixedContraction_table_1_0_2_2
  · exact b65e_fixedContraction_table_1_0_2_3
  · exact b65e_fixedContraction_table_1_0_3_0
  · exact b65e_fixedContraction_table_1_0_3_1
  · exact b65e_fixedContraction_table_1_0_3_2
  · exact b65e_fixedContraction_table_1_0_3_3
  · exact b65e_fixedContraction_table_1_1_0_0
  · exact b65e_fixedContraction_table_1_1_0_1
  · exact b65e_fixedContraction_table_1_1_0_2
  · exact b65e_fixedContraction_table_1_1_0_3
  · exact b65e_fixedContraction_table_1_1_1_0
  · exact b65e_fixedContraction_table_1_1_1_1
  · exact b65e_fixedContraction_table_1_1_1_2
  · exact b65e_fixedContraction_table_1_1_1_3
  · exact b65e_fixedContraction_table_1_1_2_0
  · exact b65e_fixedContraction_table_1_1_2_1
  · exact b65e_fixedContraction_table_1_1_2_2
  · exact b65e_fixedContraction_table_1_1_2_3
  · exact b65e_fixedContraction_table_1_1_3_0
  · exact b65e_fixedContraction_table_1_1_3_1
  · exact b65e_fixedContraction_table_1_1_3_2
  · exact b65e_fixedContraction_table_1_1_3_3
  · exact b65e_fixedContraction_table_1_2_0_0
  · exact b65e_fixedContraction_table_1_2_0_1
  · exact b65e_fixedContraction_table_1_2_0_2
  · exact b65e_fixedContraction_table_1_2_0_3
  · exact b65e_fixedContraction_table_1_2_1_0
  · exact b65e_fixedContraction_table_1_2_1_1
  · exact b65e_fixedContraction_table_1_2_1_2
  · exact b65e_fixedContraction_table_1_2_1_3
  · exact b65e_fixedContraction_table_1_2_2_0
  · exact b65e_fixedContraction_table_1_2_2_1
  · exact b65e_fixedContraction_table_1_2_2_2
  · exact b65e_fixedContraction_table_1_2_2_3
  · exact b65e_fixedContraction_table_1_2_3_0
  · exact b65e_fixedContraction_table_1_2_3_1
  · exact b65e_fixedContraction_table_1_2_3_2
  · exact b65e_fixedContraction_table_1_2_3_3
  · exact b65e_fixedContraction_table_1_3_0_0
  · exact b65e_fixedContraction_table_1_3_0_1
  · exact b65e_fixedContraction_table_1_3_0_2
  · exact b65e_fixedContraction_table_1_3_0_3
  · exact b65e_fixedContraction_table_1_3_1_0
  · exact b65e_fixedContraction_table_1_3_1_1
  · exact b65e_fixedContraction_table_1_3_1_2
  · exact b65e_fixedContraction_table_1_3_1_3
  · exact b65e_fixedContraction_table_1_3_2_0
  · exact b65e_fixedContraction_table_1_3_2_1
  · exact b65e_fixedContraction_table_1_3_2_2
  · exact b65e_fixedContraction_table_1_3_2_3
  · exact b65e_fixedContraction_table_1_3_3_0
  · exact b65e_fixedContraction_table_1_3_3_1
  · exact b65e_fixedContraction_table_1_3_3_2
  · exact b65e_fixedContraction_table_1_3_3_3

set_option maxHeartbeats 400000 in
/-- Every stored order-3 fixed-residue entry satisfies its rational contraction. -/
theorem b65e_fixedContraction_table_order3 (k i j : Fin 4) :
    b65e_fixedContractionQ 2 k i j = 3 * b65e_fixedJet 3 k i j := by
  fin_cases k <;> fin_cases i <;> fin_cases j
  · exact b65e_fixedContraction_table_2_0_0_0
  · exact b65e_fixedContraction_table_2_0_0_1
  · exact b65e_fixedContraction_table_2_0_0_2
  · exact b65e_fixedContraction_table_2_0_0_3
  · exact b65e_fixedContraction_table_2_0_1_0
  · exact b65e_fixedContraction_table_2_0_1_1
  · exact b65e_fixedContraction_table_2_0_1_2
  · exact b65e_fixedContraction_table_2_0_1_3
  · exact b65e_fixedContraction_table_2_0_2_0
  · exact b65e_fixedContraction_table_2_0_2_1
  · exact b65e_fixedContraction_table_2_0_2_2
  · exact b65e_fixedContraction_table_2_0_2_3
  · exact b65e_fixedContraction_table_2_0_3_0
  · exact b65e_fixedContraction_table_2_0_3_1
  · exact b65e_fixedContraction_table_2_0_3_2
  · exact b65e_fixedContraction_table_2_0_3_3
  · exact b65e_fixedContraction_table_2_1_0_0
  · exact b65e_fixedContraction_table_2_1_0_1
  · exact b65e_fixedContraction_table_2_1_0_2
  · exact b65e_fixedContraction_table_2_1_0_3
  · exact b65e_fixedContraction_table_2_1_1_0
  · exact b65e_fixedContraction_table_2_1_1_1
  · exact b65e_fixedContraction_table_2_1_1_2
  · exact b65e_fixedContraction_table_2_1_1_3
  · exact b65e_fixedContraction_table_2_1_2_0
  · exact b65e_fixedContraction_table_2_1_2_1
  · exact b65e_fixedContraction_table_2_1_2_2
  · exact b65e_fixedContraction_table_2_1_2_3
  · exact b65e_fixedContraction_table_2_1_3_0
  · exact b65e_fixedContraction_table_2_1_3_1
  · exact b65e_fixedContraction_table_2_1_3_2
  · exact b65e_fixedContraction_table_2_1_3_3
  · exact b65e_fixedContraction_table_2_2_0_0
  · exact b65e_fixedContraction_table_2_2_0_1
  · exact b65e_fixedContraction_table_2_2_0_2
  · exact b65e_fixedContraction_table_2_2_0_3
  · exact b65e_fixedContraction_table_2_2_1_0
  · exact b65e_fixedContraction_table_2_2_1_1
  · exact b65e_fixedContraction_table_2_2_1_2
  · exact b65e_fixedContraction_table_2_2_1_3
  · exact b65e_fixedContraction_table_2_2_2_0
  · exact b65e_fixedContraction_table_2_2_2_1
  · exact b65e_fixedContraction_table_2_2_2_2
  · exact b65e_fixedContraction_table_2_2_2_3
  · exact b65e_fixedContraction_table_2_2_3_0
  · exact b65e_fixedContraction_table_2_2_3_1
  · exact b65e_fixedContraction_table_2_2_3_2
  · exact b65e_fixedContraction_table_2_2_3_3
  · exact b65e_fixedContraction_table_2_3_0_0
  · exact b65e_fixedContraction_table_2_3_0_1
  · exact b65e_fixedContraction_table_2_3_0_2
  · exact b65e_fixedContraction_table_2_3_0_3
  · exact b65e_fixedContraction_table_2_3_1_0
  · exact b65e_fixedContraction_table_2_3_1_1
  · exact b65e_fixedContraction_table_2_3_1_2
  · exact b65e_fixedContraction_table_2_3_1_3
  · exact b65e_fixedContraction_table_2_3_2_0
  · exact b65e_fixedContraction_table_2_3_2_1
  · exact b65e_fixedContraction_table_2_3_2_2
  · exact b65e_fixedContraction_table_2_3_2_3
  · exact b65e_fixedContraction_table_2_3_3_0
  · exact b65e_fixedContraction_table_2_3_3_1
  · exact b65e_fixedContraction_table_2_3_3_2
  · exact b65e_fixedContraction_table_2_3_3_3

set_option maxHeartbeats 400000 in
/-- Every stored order-4 fixed-residue entry satisfies its rational contraction. -/
theorem b65e_fixedContraction_table_order4 (k i j : Fin 4) :
    b65e_fixedContractionQ 3 k i j = 4 * b65e_fixedJet 4 k i j := by
  fin_cases k <;> fin_cases i <;> fin_cases j
  · exact b65e_fixedContraction_table_3_0_0_0
  · exact b65e_fixedContraction_table_3_0_0_1
  · exact b65e_fixedContraction_table_3_0_0_2
  · exact b65e_fixedContraction_table_3_0_0_3
  · exact b65e_fixedContraction_table_3_0_1_0
  · exact b65e_fixedContraction_table_3_0_1_1
  · exact b65e_fixedContraction_table_3_0_1_2
  · exact b65e_fixedContraction_table_3_0_1_3
  · exact b65e_fixedContraction_table_3_0_2_0
  · exact b65e_fixedContraction_table_3_0_2_1
  · exact b65e_fixedContraction_table_3_0_2_2
  · exact b65e_fixedContraction_table_3_0_2_3
  · exact b65e_fixedContraction_table_3_0_3_0
  · exact b65e_fixedContraction_table_3_0_3_1
  · exact b65e_fixedContraction_table_3_0_3_2
  · exact b65e_fixedContraction_table_3_0_3_3
  · exact b65e_fixedContraction_table_3_1_0_0
  · exact b65e_fixedContraction_table_3_1_0_1
  · exact b65e_fixedContraction_table_3_1_0_2
  · exact b65e_fixedContraction_table_3_1_0_3
  · exact b65e_fixedContraction_table_3_1_1_0
  · exact b65e_fixedContraction_table_3_1_1_1
  · exact b65e_fixedContraction_table_3_1_1_2
  · exact b65e_fixedContraction_table_3_1_1_3
  · exact b65e_fixedContraction_table_3_1_2_0
  · exact b65e_fixedContraction_table_3_1_2_1
  · exact b65e_fixedContraction_table_3_1_2_2
  · exact b65e_fixedContraction_table_3_1_2_3
  · exact b65e_fixedContraction_table_3_1_3_0
  · exact b65e_fixedContraction_table_3_1_3_1
  · exact b65e_fixedContraction_table_3_1_3_2
  · exact b65e_fixedContraction_table_3_1_3_3
  · exact b65e_fixedContraction_table_3_2_0_0
  · exact b65e_fixedContraction_table_3_2_0_1
  · exact b65e_fixedContraction_table_3_2_0_2
  · exact b65e_fixedContraction_table_3_2_0_3
  · exact b65e_fixedContraction_table_3_2_1_0
  · exact b65e_fixedContraction_table_3_2_1_1
  · exact b65e_fixedContraction_table_3_2_1_2
  · exact b65e_fixedContraction_table_3_2_1_3
  · exact b65e_fixedContraction_table_3_2_2_0
  · exact b65e_fixedContraction_table_3_2_2_1
  · exact b65e_fixedContraction_table_3_2_2_2
  · exact b65e_fixedContraction_table_3_2_2_3
  · exact b65e_fixedContraction_table_3_2_3_0
  · exact b65e_fixedContraction_table_3_2_3_1
  · exact b65e_fixedContraction_table_3_2_3_2
  · exact b65e_fixedContraction_table_3_2_3_3
  · exact b65e_fixedContraction_table_3_3_0_0
  · exact b65e_fixedContraction_table_3_3_0_1
  · exact b65e_fixedContraction_table_3_3_0_2
  · exact b65e_fixedContraction_table_3_3_0_3
  · exact b65e_fixedContraction_table_3_3_1_0
  · exact b65e_fixedContraction_table_3_3_1_1
  · exact b65e_fixedContraction_table_3_3_1_2
  · exact b65e_fixedContraction_table_3_3_1_3
  · exact b65e_fixedContraction_table_3_3_2_0
  · exact b65e_fixedContraction_table_3_3_2_1
  · exact b65e_fixedContraction_table_3_3_2_2
  · exact b65e_fixedContraction_table_3_3_2_3
  · exact b65e_fixedContraction_table_3_3_3_0
  · exact b65e_fixedContraction_table_3_3_3_1
  · exact b65e_fixedContraction_table_3_3_3_2
  · exact b65e_fixedContraction_table_3_3_3_3

set_option maxHeartbeats 400000 in
/-- Every stored order-5 fixed-residue entry satisfies its rational contraction. -/
theorem b65e_fixedContraction_table_order5 (k i j : Fin 4) :
    b65e_fixedContractionQ 4 k i j = 5 * b65e_fixedJet 5 k i j := by
  fin_cases k <;> fin_cases i <;> fin_cases j
  · exact b65e_fixedContraction_table_4_0_0_0
  · exact b65e_fixedContraction_table_4_0_0_1
  · exact b65e_fixedContraction_table_4_0_0_2
  · exact b65e_fixedContraction_table_4_0_0_3
  · exact b65e_fixedContraction_table_4_0_1_0
  · exact b65e_fixedContraction_table_4_0_1_1
  · exact b65e_fixedContraction_table_4_0_1_2
  · exact b65e_fixedContraction_table_4_0_1_3
  · exact b65e_fixedContraction_table_4_0_2_0
  · exact b65e_fixedContraction_table_4_0_2_1
  · exact b65e_fixedContraction_table_4_0_2_2
  · exact b65e_fixedContraction_table_4_0_2_3
  · exact b65e_fixedContraction_table_4_0_3_0
  · exact b65e_fixedContraction_table_4_0_3_1
  · exact b65e_fixedContraction_table_4_0_3_2
  · exact b65e_fixedContraction_table_4_0_3_3
  · exact b65e_fixedContraction_table_4_1_0_0
  · exact b65e_fixedContraction_table_4_1_0_1
  · exact b65e_fixedContraction_table_4_1_0_2
  · exact b65e_fixedContraction_table_4_1_0_3
  · exact b65e_fixedContraction_table_4_1_1_0
  · exact b65e_fixedContraction_table_4_1_1_1
  · exact b65e_fixedContraction_table_4_1_1_2
  · exact b65e_fixedContraction_table_4_1_1_3
  · exact b65e_fixedContraction_table_4_1_2_0
  · exact b65e_fixedContraction_table_4_1_2_1
  · exact b65e_fixedContraction_table_4_1_2_2
  · exact b65e_fixedContraction_table_4_1_2_3
  · exact b65e_fixedContraction_table_4_1_3_0
  · exact b65e_fixedContraction_table_4_1_3_1
  · exact b65e_fixedContraction_table_4_1_3_2
  · exact b65e_fixedContraction_table_4_1_3_3
  · exact b65e_fixedContraction_table_4_2_0_0
  · exact b65e_fixedContraction_table_4_2_0_1
  · exact b65e_fixedContraction_table_4_2_0_2
  · exact b65e_fixedContraction_table_4_2_0_3
  · exact b65e_fixedContraction_table_4_2_1_0
  · exact b65e_fixedContraction_table_4_2_1_1
  · exact b65e_fixedContraction_table_4_2_1_2
  · exact b65e_fixedContraction_table_4_2_1_3
  · exact b65e_fixedContraction_table_4_2_2_0
  · exact b65e_fixedContraction_table_4_2_2_1
  · exact b65e_fixedContraction_table_4_2_2_2
  · exact b65e_fixedContraction_table_4_2_2_3
  · exact b65e_fixedContraction_table_4_2_3_0
  · exact b65e_fixedContraction_table_4_2_3_1
  · exact b65e_fixedContraction_table_4_2_3_2
  · exact b65e_fixedContraction_table_4_2_3_3
  · exact b65e_fixedContraction_table_4_3_0_0
  · exact b65e_fixedContraction_table_4_3_0_1
  · exact b65e_fixedContraction_table_4_3_0_2
  · exact b65e_fixedContraction_table_4_3_0_3
  · exact b65e_fixedContraction_table_4_3_1_0
  · exact b65e_fixedContraction_table_4_3_1_1
  · exact b65e_fixedContraction_table_4_3_1_2
  · exact b65e_fixedContraction_table_4_3_1_3
  · exact b65e_fixedContraction_table_4_3_2_0
  · exact b65e_fixedContraction_table_4_3_2_1
  · exact b65e_fixedContraction_table_4_3_2_2
  · exact b65e_fixedContraction_table_4_3_2_3
  · exact b65e_fixedContraction_table_4_3_3_0
  · exact b65e_fixedContraction_table_4_3_3_1
  · exact b65e_fixedContraction_table_4_3_3_2
  · exact b65e_fixedContraction_table_4_3_3_3

set_option maxHeartbeats 400000 in
/-- Every stored order-6 fixed-residue entry satisfies its rational contraction. -/
theorem b65e_fixedContraction_table_order6 (k i j : Fin 4) :
    b65e_fixedContractionQ 5 k i j = 6 * b65e_fixedJet 6 k i j := by
  fin_cases k <;> fin_cases i <;> fin_cases j
  · exact b65e_fixedContraction_table_5_0_0_0
  · exact b65e_fixedContraction_table_5_0_0_1
  · exact b65e_fixedContraction_table_5_0_0_2
  · exact b65e_fixedContraction_table_5_0_0_3
  · exact b65e_fixedContraction_table_5_0_1_0
  · exact b65e_fixedContraction_table_5_0_1_1
  · exact b65e_fixedContraction_table_5_0_1_2
  · exact b65e_fixedContraction_table_5_0_1_3
  · exact b65e_fixedContraction_table_5_0_2_0
  · exact b65e_fixedContraction_table_5_0_2_1
  · exact b65e_fixedContraction_table_5_0_2_2
  · exact b65e_fixedContraction_table_5_0_2_3
  · exact b65e_fixedContraction_table_5_0_3_0
  · exact b65e_fixedContraction_table_5_0_3_1
  · exact b65e_fixedContraction_table_5_0_3_2
  · exact b65e_fixedContraction_table_5_0_3_3
  · exact b65e_fixedContraction_table_5_1_0_0
  · exact b65e_fixedContraction_table_5_1_0_1
  · exact b65e_fixedContraction_table_5_1_0_2
  · exact b65e_fixedContraction_table_5_1_0_3
  · exact b65e_fixedContraction_table_5_1_1_0
  · exact b65e_fixedContraction_table_5_1_1_1
  · exact b65e_fixedContraction_table_5_1_1_2
  · exact b65e_fixedContraction_table_5_1_1_3
  · exact b65e_fixedContraction_table_5_1_2_0
  · exact b65e_fixedContraction_table_5_1_2_1
  · exact b65e_fixedContraction_table_5_1_2_2
  · exact b65e_fixedContraction_table_5_1_2_3
  · exact b65e_fixedContraction_table_5_1_3_0
  · exact b65e_fixedContraction_table_5_1_3_1
  · exact b65e_fixedContraction_table_5_1_3_2
  · exact b65e_fixedContraction_table_5_1_3_3
  · exact b65e_fixedContraction_table_5_2_0_0
  · exact b65e_fixedContraction_table_5_2_0_1
  · exact b65e_fixedContraction_table_5_2_0_2
  · exact b65e_fixedContraction_table_5_2_0_3
  · exact b65e_fixedContraction_table_5_2_1_0
  · exact b65e_fixedContraction_table_5_2_1_1
  · exact b65e_fixedContraction_table_5_2_1_2
  · exact b65e_fixedContraction_table_5_2_1_3
  · exact b65e_fixedContraction_table_5_2_2_0
  · exact b65e_fixedContraction_table_5_2_2_1
  · exact b65e_fixedContraction_table_5_2_2_2
  · exact b65e_fixedContraction_table_5_2_2_3
  · exact b65e_fixedContraction_table_5_2_3_0
  · exact b65e_fixedContraction_table_5_2_3_1
  · exact b65e_fixedContraction_table_5_2_3_2
  · exact b65e_fixedContraction_table_5_2_3_3
  · exact b65e_fixedContraction_table_5_3_0_0
  · exact b65e_fixedContraction_table_5_3_0_1
  · exact b65e_fixedContraction_table_5_3_0_2
  · exact b65e_fixedContraction_table_5_3_0_3
  · exact b65e_fixedContraction_table_5_3_1_0
  · exact b65e_fixedContraction_table_5_3_1_1
  · exact b65e_fixedContraction_table_5_3_1_2
  · exact b65e_fixedContraction_table_5_3_1_3
  · exact b65e_fixedContraction_table_5_3_2_0
  · exact b65e_fixedContraction_table_5_3_2_1
  · exact b65e_fixedContraction_table_5_3_2_2
  · exact b65e_fixedContraction_table_5_3_2_3
  · exact b65e_fixedContraction_table_5_3_3_0
  · exact b65e_fixedContraction_table_5_3_3_1
  · exact b65e_fixedContraction_table_5_3_3_2
  · exact b65e_fixedContraction_table_5_3_3_3

set_option maxHeartbeats 400000 in
/-- Every stored order-7 fixed-residue entry satisfies its rational contraction. -/
theorem b65e_fixedContraction_table_order7 (k i j : Fin 4) :
    b65e_fixedContractionQ 6 k i j = 7 * b65e_fixedJet 7 k i j := by
  fin_cases k <;> fin_cases i <;> fin_cases j
  · exact b65e_fixedContraction_table_6_0_0_0
  · exact b65e_fixedContraction_table_6_0_0_1
  · exact b65e_fixedContraction_table_6_0_0_2
  · exact b65e_fixedContraction_table_6_0_0_3
  · exact b65e_fixedContraction_table_6_0_1_0
  · exact b65e_fixedContraction_table_6_0_1_1
  · exact b65e_fixedContraction_table_6_0_1_2
  · exact b65e_fixedContraction_table_6_0_1_3
  · exact b65e_fixedContraction_table_6_0_2_0
  · exact b65e_fixedContraction_table_6_0_2_1
  · exact b65e_fixedContraction_table_6_0_2_2
  · exact b65e_fixedContraction_table_6_0_2_3
  · exact b65e_fixedContraction_table_6_0_3_0
  · exact b65e_fixedContraction_table_6_0_3_1
  · exact b65e_fixedContraction_table_6_0_3_2
  · exact b65e_fixedContraction_table_6_0_3_3
  · exact b65e_fixedContraction_table_6_1_0_0
  · exact b65e_fixedContraction_table_6_1_0_1
  · exact b65e_fixedContraction_table_6_1_0_2
  · exact b65e_fixedContraction_table_6_1_0_3
  · exact b65e_fixedContraction_table_6_1_1_0
  · exact b65e_fixedContraction_table_6_1_1_1
  · exact b65e_fixedContraction_table_6_1_1_2
  · exact b65e_fixedContraction_table_6_1_1_3
  · exact b65e_fixedContraction_table_6_1_2_0
  · exact b65e_fixedContraction_table_6_1_2_1
  · exact b65e_fixedContraction_table_6_1_2_2
  · exact b65e_fixedContraction_table_6_1_2_3
  · exact b65e_fixedContraction_table_6_1_3_0
  · exact b65e_fixedContraction_table_6_1_3_1
  · exact b65e_fixedContraction_table_6_1_3_2
  · exact b65e_fixedContraction_table_6_1_3_3
  · exact b65e_fixedContraction_table_6_2_0_0
  · exact b65e_fixedContraction_table_6_2_0_1
  · exact b65e_fixedContraction_table_6_2_0_2
  · exact b65e_fixedContraction_table_6_2_0_3
  · exact b65e_fixedContraction_table_6_2_1_0
  · exact b65e_fixedContraction_table_6_2_1_1
  · exact b65e_fixedContraction_table_6_2_1_2
  · exact b65e_fixedContraction_table_6_2_1_3
  · exact b65e_fixedContraction_table_6_2_2_0
  · exact b65e_fixedContraction_table_6_2_2_1
  · exact b65e_fixedContraction_table_6_2_2_2
  · exact b65e_fixedContraction_table_6_2_2_3
  · exact b65e_fixedContraction_table_6_2_3_0
  · exact b65e_fixedContraction_table_6_2_3_1
  · exact b65e_fixedContraction_table_6_2_3_2
  · exact b65e_fixedContraction_table_6_2_3_3
  · exact b65e_fixedContraction_table_6_3_0_0
  · exact b65e_fixedContraction_table_6_3_0_1
  · exact b65e_fixedContraction_table_6_3_0_2
  · exact b65e_fixedContraction_table_6_3_0_3
  · exact b65e_fixedContraction_table_6_3_1_0
  · exact b65e_fixedContraction_table_6_3_1_1
  · exact b65e_fixedContraction_table_6_3_1_2
  · exact b65e_fixedContraction_table_6_3_1_3
  · exact b65e_fixedContraction_table_6_3_2_0
  · exact b65e_fixedContraction_table_6_3_2_1
  · exact b65e_fixedContraction_table_6_3_2_2
  · exact b65e_fixedContraction_table_6_3_2_3
  · exact b65e_fixedContraction_table_6_3_3_0
  · exact b65e_fixedContraction_table_6_3_3_1
  · exact b65e_fixedContraction_table_6_3_3_2
  · exact b65e_fixedContraction_table_6_3_3_3

/-- The stored fixed-residue coefficients at orders two through seven satisfy the
finite rational Schlesinger contractions. -/
theorem b65e_fixedContraction_table (n : Fin 6) (k i j : Fin 4) :
    b65e_fixedContractionQ n.succ k i j =
      (n.val + 2 : ℚ) * b65e_fixedJet n.succ.succ k i j := by
  fin_cases n
  · convert b65e_fixedContraction_table_order2 k i j using 1 <;> norm_num
  · convert b65e_fixedContraction_table_order3 k i j using 1 <;> norm_num
  · convert b65e_fixedContraction_table_order4 k i j using 1 <;> norm_num
  · convert b65e_fixedContraction_table_order5 k i j using 1 <;> norm_num
  · convert b65e_fixedContraction_table_order6 k i j using 1 <;> norm_num
  · convert b65e_fixedContraction_table_order7 k i j using 1 <;> norm_num

end HodgeLean.Foundations.Program
