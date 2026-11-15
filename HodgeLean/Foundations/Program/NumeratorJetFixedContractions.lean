import HodgeLean.Foundations.Program.NumeratorJetFixedWeightEvaluation
import HodgeLean.Foundations.Program.NumeratorJetPowerMoments
import HodgeLean.Foundations.Program.NumeratorJetFixedCertificates

/-! # Finite rational contractions for stored fixed-pole recurrences -/

noncomputable section
open Polynomial Matrix
namespace HodgeLean.Foundations.Program

/-- Trace of a reduced geometric weight times a coordinate monomial. -/
def b65e_weightMomentQ (n : Fin 7) (e : Fin 2) (k : Fin 4) (d : Fin 6) : ℚ :=
  ∑ c : Fin 6, b65e_fixedWeightCoeffQ n e k c *
    b65e_powerMomentQ ⟨c.val + d.val, by omega⟩ e

/-- Weighted trace of a stored moving-residue entry. -/
def b65e_weightedMovingQ (n : Fin 7) (b : Fin 8) (e : Fin 2)
    (k : Fin 4) (i j : Fin 4) : ℚ :=
  ∑ d : Fin 6, b65e_movingJet b e d i j * b65e_weightMomentQ n e k d

/-- Finite rational fixed-pole Schlesinger convolution on the stored arrays. -/
def b65e_fixedContractionQ (n : Fin 7) (k : Fin 4) (i j : Fin 4) : ℚ :=
  ∑ e : Fin 2, ∑ a ∈ Finset.range (n.val + 1),
    ∑ t : Fin 4, ∑ b ∈ Finset.range (n.val - a + 1),
      (b65e_weightedMovingQ (Fin.ofNat 7 a) (Fin.ofNat 8 b) e k i t *
        b65e_fixedJet (Fin.ofNat 8 (n.val - a - b)) k t j -
      b65e_fixedJet (Fin.ofNat 8 b) k i t *
        b65e_weightedMovingQ (Fin.ofNat 7 a) (Fin.ofNat 8 (n.val - a - b)) e k t j)

set_option maxHeartbeats 400000 in
/-- Stored order-two entry at the first fixed pole satisfies the rational field recursion. -/
theorem b65e_fixedContraction_table_1_0_0_0 :
    b65e_fixedContractionQ 1 0 0 0 = 2 * b65e_fixedJet 2 0 0 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_0_0_1 :
    b65e_fixedContractionQ 1 0 0 1 = 2 * b65e_fixedJet 2 0 0 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_0_0_2 :
    b65e_fixedContractionQ 1 0 0 2 = 2 * b65e_fixedJet 2 0 0 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_0_0_3 :
    b65e_fixedContractionQ 1 0 0 3 = 2 * b65e_fixedJet 2 0 0 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_0_1_0 :
    b65e_fixedContractionQ 1 0 1 0 = 2 * b65e_fixedJet 2 0 1 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_0_1_1 :
    b65e_fixedContractionQ 1 0 1 1 = 2 * b65e_fixedJet 2 0 1 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_0_1_2 :
    b65e_fixedContractionQ 1 0 1 2 = 2 * b65e_fixedJet 2 0 1 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_0_1_3 :
    b65e_fixedContractionQ 1 0 1 3 = 2 * b65e_fixedJet 2 0 1 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_0_2_0 :
    b65e_fixedContractionQ 1 0 2 0 = 2 * b65e_fixedJet 2 0 2 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_0_2_1 :
    b65e_fixedContractionQ 1 0 2 1 = 2 * b65e_fixedJet 2 0 2 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_0_2_2 :
    b65e_fixedContractionQ 1 0 2 2 = 2 * b65e_fixedJet 2 0 2 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_0_2_3 :
    b65e_fixedContractionQ 1 0 2 3 = 2 * b65e_fixedJet 2 0 2 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_0_3_0 :
    b65e_fixedContractionQ 1 0 3 0 = 2 * b65e_fixedJet 2 0 3 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_0_3_1 :
    b65e_fixedContractionQ 1 0 3 1 = 2 * b65e_fixedJet 2 0 3 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_0_3_2 :
    b65e_fixedContractionQ 1 0 3 2 = 2 * b65e_fixedJet 2 0 3 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_0_3_3 :
    b65e_fixedContractionQ 1 0 3 3 = 2 * b65e_fixedJet 2 0 3 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_1_0_0 :
    b65e_fixedContractionQ 1 1 0 0 = 2 * b65e_fixedJet 2 1 0 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_1_0_1 :
    b65e_fixedContractionQ 1 1 0 1 = 2 * b65e_fixedJet 2 1 0 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_1_0_2 :
    b65e_fixedContractionQ 1 1 0 2 = 2 * b65e_fixedJet 2 1 0 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_1_0_3 :
    b65e_fixedContractionQ 1 1 0 3 = 2 * b65e_fixedJet 2 1 0 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_1_1_0 :
    b65e_fixedContractionQ 1 1 1 0 = 2 * b65e_fixedJet 2 1 1 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_1_1_1 :
    b65e_fixedContractionQ 1 1 1 1 = 2 * b65e_fixedJet 2 1 1 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_1_1_2 :
    b65e_fixedContractionQ 1 1 1 2 = 2 * b65e_fixedJet 2 1 1 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_1_1_3 :
    b65e_fixedContractionQ 1 1 1 3 = 2 * b65e_fixedJet 2 1 1 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_1_2_0 :
    b65e_fixedContractionQ 1 1 2 0 = 2 * b65e_fixedJet 2 1 2 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_1_2_1 :
    b65e_fixedContractionQ 1 1 2 1 = 2 * b65e_fixedJet 2 1 2 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_1_2_2 :
    b65e_fixedContractionQ 1 1 2 2 = 2 * b65e_fixedJet 2 1 2 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_1_2_3 :
    b65e_fixedContractionQ 1 1 2 3 = 2 * b65e_fixedJet 2 1 2 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_1_3_0 :
    b65e_fixedContractionQ 1 1 3 0 = 2 * b65e_fixedJet 2 1 3 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_1_3_1 :
    b65e_fixedContractionQ 1 1 3 1 = 2 * b65e_fixedJet 2 1 3 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_1_3_2 :
    b65e_fixedContractionQ 1 1 3 2 = 2 * b65e_fixedJet 2 1 3 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_1_3_3 :
    b65e_fixedContractionQ 1 1 3 3 = 2 * b65e_fixedJet 2 1 3 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_2_0_0 :
    b65e_fixedContractionQ 1 2 0 0 = 2 * b65e_fixedJet 2 2 0 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_2_0_1 :
    b65e_fixedContractionQ 1 2 0 1 = 2 * b65e_fixedJet 2 2 0 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_2_0_2 :
    b65e_fixedContractionQ 1 2 0 2 = 2 * b65e_fixedJet 2 2 0 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_2_0_3 :
    b65e_fixedContractionQ 1 2 0 3 = 2 * b65e_fixedJet 2 2 0 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_2_1_0 :
    b65e_fixedContractionQ 1 2 1 0 = 2 * b65e_fixedJet 2 2 1 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_2_1_1 :
    b65e_fixedContractionQ 1 2 1 1 = 2 * b65e_fixedJet 2 2 1 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_2_1_2 :
    b65e_fixedContractionQ 1 2 1 2 = 2 * b65e_fixedJet 2 2 1 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_2_1_3 :
    b65e_fixedContractionQ 1 2 1 3 = 2 * b65e_fixedJet 2 2 1 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_2_2_0 :
    b65e_fixedContractionQ 1 2 2 0 = 2 * b65e_fixedJet 2 2 2 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_2_2_1 :
    b65e_fixedContractionQ 1 2 2 1 = 2 * b65e_fixedJet 2 2 2 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_2_2_2 :
    b65e_fixedContractionQ 1 2 2 2 = 2 * b65e_fixedJet 2 2 2 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_2_2_3 :
    b65e_fixedContractionQ 1 2 2 3 = 2 * b65e_fixedJet 2 2 2 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_2_3_0 :
    b65e_fixedContractionQ 1 2 3 0 = 2 * b65e_fixedJet 2 2 3 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_2_3_1 :
    b65e_fixedContractionQ 1 2 3 1 = 2 * b65e_fixedJet 2 2 3 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_2_3_2 :
    b65e_fixedContractionQ 1 2 3 2 = 2 * b65e_fixedJet 2 2 3 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_2_3_3 :
    b65e_fixedContractionQ 1 2 3 3 = 2 * b65e_fixedJet 2 2 3 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_3_0_0 :
    b65e_fixedContractionQ 1 3 0 0 = 2 * b65e_fixedJet 2 3 0 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_3_0_1 :
    b65e_fixedContractionQ 1 3 0 1 = 2 * b65e_fixedJet 2 3 0 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_3_0_2 :
    b65e_fixedContractionQ 1 3 0 2 = 2 * b65e_fixedJet 2 3 0 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_3_0_3 :
    b65e_fixedContractionQ 1 3 0 3 = 2 * b65e_fixedJet 2 3 0 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_3_1_0 :
    b65e_fixedContractionQ 1 3 1 0 = 2 * b65e_fixedJet 2 3 1 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_3_1_1 :
    b65e_fixedContractionQ 1 3 1 1 = 2 * b65e_fixedJet 2 3 1 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_3_1_2 :
    b65e_fixedContractionQ 1 3 1 2 = 2 * b65e_fixedJet 2 3 1 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_3_1_3 :
    b65e_fixedContractionQ 1 3 1 3 = 2 * b65e_fixedJet 2 3 1 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_3_2_0 :
    b65e_fixedContractionQ 1 3 2 0 = 2 * b65e_fixedJet 2 3 2 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_3_2_1 :
    b65e_fixedContractionQ 1 3 2 1 = 2 * b65e_fixedJet 2 3 2 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_3_2_2 :
    b65e_fixedContractionQ 1 3 2 2 = 2 * b65e_fixedJet 2 3 2 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_3_2_3 :
    b65e_fixedContractionQ 1 3 2 3 = 2 * b65e_fixedJet 2 3 2 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_3_3_0 :
    b65e_fixedContractionQ 1 3 3 0 = 2 * b65e_fixedJet 2 3 3 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_3_3_1 :
    b65e_fixedContractionQ 1 3 3 1 = 2 * b65e_fixedJet 2 3 3 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_3_3_2 :
    b65e_fixedContractionQ 1 3 3 2 = 2 * b65e_fixedJet 2 3 3 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Stored order-two entry satisfies the rational fixed-pole field recursion. -/
theorem b65e_fixedContraction_table_1_3_3_3 :
    b65e_fixedContractionQ 1 3 3 3 = 2 * b65e_fixedJet 2 3 3 3 := by
  decide +kernel

end HodgeLean.Foundations.Program
