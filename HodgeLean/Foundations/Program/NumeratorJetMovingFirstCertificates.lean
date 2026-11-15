import HodgeLean.Foundations.Program.NumeratorJetMovingTraceReduction

/-! # Rational certificates for the first moving-residue coefficients -/

noncomputable section
open Polynomial Matrix
namespace HodgeLean.Foundations.Program

/-- First moving field in reduced sextic coordinates. -/
def b65e_movingFirstCoeffQ (e : Fin 2) (c : Fin 6) (i j : Fin 4) : ℚ :=
  (∑ k : Fin 4, b65e_fixedWeightCoeffQ 0 e k c *
    (b65q_fixedResQ k * b65q_BQ e - b65q_BQ e * b65q_fixedResQ k) i j) +
  ∑ d : Fin 2, b65e_reducedMovingTraceCoeffQ e d c *
    (b65q_BQ d * b65q_BQ e - b65q_BQ e * b65q_BQ d) i j

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_0_0_0 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 0 c 0 0 = b65e_movingJet 1 0 c 0 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_0_0_1 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 0 c 0 1 = b65e_movingJet 1 0 c 0 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_0_0_2 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 0 c 0 2 = b65e_movingJet 1 0 c 0 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_0_0_3 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 0 c 0 3 = b65e_movingJet 1 0 c 0 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_0_1_0 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 0 c 1 0 = b65e_movingJet 1 0 c 1 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_0_1_1 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 0 c 1 1 = b65e_movingJet 1 0 c 1 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_0_1_2 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 0 c 1 2 = b65e_movingJet 1 0 c 1 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_0_1_3 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 0 c 1 3 = b65e_movingJet 1 0 c 1 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_0_2_0 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 0 c 2 0 = b65e_movingJet 1 0 c 2 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_0_2_1 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 0 c 2 1 = b65e_movingJet 1 0 c 2 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_0_2_2 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 0 c 2 2 = b65e_movingJet 1 0 c 2 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_0_2_3 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 0 c 2 3 = b65e_movingJet 1 0 c 2 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_0_3_0 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 0 c 3 0 = b65e_movingJet 1 0 c 3 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_0_3_1 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 0 c 3 1 = b65e_movingJet 1 0 c 3 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_0_3_2 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 0 c 3 2 = b65e_movingJet 1 0 c 3 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_0_3_3 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 0 c 3 3 = b65e_movingJet 1 0 c 3 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_1_0_0 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 1 c 0 0 = b65e_movingJet 1 1 c 0 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_1_0_1 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 1 c 0 1 = b65e_movingJet 1 1 c 0 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_1_0_2 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 1 c 0 2 = b65e_movingJet 1 1 c 0 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_1_0_3 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 1 c 0 3 = b65e_movingJet 1 1 c 0 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_1_1_0 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 1 c 1 0 = b65e_movingJet 1 1 c 1 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_1_1_1 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 1 c 1 1 = b65e_movingJet 1 1 c 1 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_1_1_2 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 1 c 1 2 = b65e_movingJet 1 1 c 1 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_1_1_3 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 1 c 1 3 = b65e_movingJet 1 1 c 1 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_1_2_0 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 1 c 2 0 = b65e_movingJet 1 1 c 2 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_1_2_1 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 1 c 2 1 = b65e_movingJet 1 1 c 2 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_1_2_2 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 1 c 2 2 = b65e_movingJet 1 1 c 2 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_1_2_3 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 1 c 2 3 = b65e_movingJet 1 1 c 2 3 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_1_3_0 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 1 c 3 0 = b65e_movingJet 1 1 c 3 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_1_3_1 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 1 c 3 1 = b65e_movingJet 1 1 c 3 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_1_3_2 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 1 c 3 2 = b65e_movingJet 1 1 c 3 2 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Rational coordinate check for a first moving-residue entry. -/
theorem b65e_movingFirst_table_1_3_3 : ∀ c : Fin 6,
    b65e_movingFirstCoeffQ 1 c 3 3 = b65e_movingJet 1 1 c 3 3 := by
  decide +kernel

/-- All first moving-residue coordinates satisfy the reduced initial field. -/
theorem b65e_movingFirst_table (e : Fin 2) (c : Fin 6) (i j : Fin 4) :
    b65e_movingFirstCoeffQ e c i j = b65e_movingJet 1 e c i j := by
  fin_cases e <;> fin_cases i <;> fin_cases j
  · exact b65e_movingFirst_table_0_0_0 c
  · exact b65e_movingFirst_table_0_0_1 c
  · exact b65e_movingFirst_table_0_0_2 c
  · exact b65e_movingFirst_table_0_0_3 c
  · exact b65e_movingFirst_table_0_1_0 c
  · exact b65e_movingFirst_table_0_1_1 c
  · exact b65e_movingFirst_table_0_1_2 c
  · exact b65e_movingFirst_table_0_1_3 c
  · exact b65e_movingFirst_table_0_2_0 c
  · exact b65e_movingFirst_table_0_2_1 c
  · exact b65e_movingFirst_table_0_2_2 c
  · exact b65e_movingFirst_table_0_2_3 c
  · exact b65e_movingFirst_table_0_3_0 c
  · exact b65e_movingFirst_table_0_3_1 c
  · exact b65e_movingFirst_table_0_3_2 c
  · exact b65e_movingFirst_table_0_3_3 c
  · exact b65e_movingFirst_table_1_0_0 c
  · exact b65e_movingFirst_table_1_0_1 c
  · exact b65e_movingFirst_table_1_0_2 c
  · exact b65e_movingFirst_table_1_0_3 c
  · exact b65e_movingFirst_table_1_1_0 c
  · exact b65e_movingFirst_table_1_1_1 c
  · exact b65e_movingFirst_table_1_1_2 c
  · exact b65e_movingFirst_table_1_1_3 c
  · exact b65e_movingFirst_table_1_2_0 c
  · exact b65e_movingFirst_table_1_2_1 c
  · exact b65e_movingFirst_table_1_2_2 c
  · exact b65e_movingFirst_table_1_2_3 c
  · exact b65e_movingFirst_table_1_3_0 c
  · exact b65e_movingFirst_table_1_3_1 c
  · exact b65e_movingFirst_table_1_3_2 c
  · exact b65e_movingFirst_table_1_3_3 c

end HodgeLean.Foundations.Program
