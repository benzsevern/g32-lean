import HodgeLean.Foundations.Program.NumeratorJetGaugeDefs

/-! # Gauge and Laurent coefficient checks at fixed pole 2 -/

namespace HodgeLean.Foundations.Program
open Matrix

set_option maxHeartbeats 400000 in
/-- Conjugated regular-part jets at pole 2. -/
theorem b65e_conjJet_table_2 : ∀ l : Fin 5, ∀ n : Fin 8,
    b65e_conjJetQ 2 l n =
      b65e_convQ (b65e_basisInvN 2) (b65e_convQ (b65e_taylorN 2 l) (b65e_basisN 2)) n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Initial gauge jets at pole 2. -/
theorem b65e_gaugeJet_zero_2 : ∀ n : Fin 8,
    b65e_gaugeJetQ 2 0 n = if n.val = 0 then 1 else 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Gauge recursion at pole 2, index 1. -/
theorem b65e_gaugeJet_table_2_1 : ∀ n : Fin 8,
    b65e_gaugeJetQ 2 1 n = b65e_gaugeRhsQ 2 1 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Gauge recursion at pole 2, index 2. -/
theorem b65e_gaugeJet_table_2_2 : ∀ n : Fin 8,
    b65e_gaugeJetQ 2 2 n = b65e_gaugeRhsQ 2 2 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Gauge recursion at pole 2, index 3. -/
theorem b65e_gaugeJet_table_2_3 : ∀ n : Fin 8,
    b65e_gaugeJetQ 2 3 n = b65e_gaugeRhsQ 2 3 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Gauge recursion at pole 2, index 4. -/
theorem b65e_gaugeJet_table_2_4 : ∀ n : Fin 8,
    b65e_gaugeJetQ 2 4 n = b65e_gaugeRhsQ 2 4 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Gauge recursion at pole 2, index 5. -/
theorem b65e_gaugeJet_table_2_5 : ∀ n : Fin 8,
    b65e_gaugeJetQ 2 5 n = b65e_gaugeRhsQ 2 5 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Initial inverse gauge jets at pole 2. -/
theorem b65e_gaugeInvJet_zero_2 : ∀ n : Fin 8,
    b65e_gaugeInvJetQ 2 0 n = if n.val = 0 then 1 else 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Inverse-series recursion at pole 2. -/
theorem b65e_gaugeInvJet_table_2 : ∀ m : Fin 6, ∀ n : Fin 8, m.val ≠ 0 →
    b65e_gaugeInvJetQ 2 m n = b65e_gaugeInvRhsQ 2 m n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- r-coefficient jets at pole 2. -/
theorem b65e_rCoeffJet_table_2 : ∀ m : Fin 6, ∀ n : Fin 8,
    b65e_rCoeffJetQ 2 m n = b65e_convQ (b65e_gaugeInvN 2 m) (b65e_basisInvN 2) n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- q-coefficient jets at pole 2. -/
theorem b65e_qCoeffJet_table_2 : ∀ m : Fin 6, ∀ n : Fin 8,
    b65e_qCoeffJetQ 2 m n = (b65e_convQ (b65e_basisN 2) (b65e_gaugeN 2 m) n)ᵀ := by
  decide +kernel

end HodgeLean.Foundations.Program
