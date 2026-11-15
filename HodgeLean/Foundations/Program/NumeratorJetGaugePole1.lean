import HodgeLean.Foundations.Program.NumeratorJetGaugeDefs

/-! # Gauge and Laurent coefficient checks at fixed pole 1 -/

namespace HodgeLean.Foundations.Program
open Matrix

set_option maxHeartbeats 400000 in
/-- Conjugated regular-part jets at pole 1. -/
theorem b65e_conjJet_table_1 : ∀ l : Fin 5, ∀ n : Fin 8,
    b65e_conjJetQ 1 l n =
      b65e_convQ (b65e_basisInvN 1) (b65e_convQ (b65e_taylorN 1 l) (b65e_basisN 1)) n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Initial gauge jets at pole 1. -/
theorem b65e_gaugeJet_zero_1 : ∀ n : Fin 8,
    b65e_gaugeJetQ 1 0 n = if n.val = 0 then 1 else 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Gauge recursion at pole 1, index 1. -/
theorem b65e_gaugeJet_table_1_1 : ∀ n : Fin 8,
    b65e_gaugeJetQ 1 1 n = b65e_gaugeRhsQ 1 1 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Gauge recursion at pole 1, index 2. -/
theorem b65e_gaugeJet_table_1_2 : ∀ n : Fin 8,
    b65e_gaugeJetQ 1 2 n = b65e_gaugeRhsQ 1 2 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Gauge recursion at pole 1, index 3. -/
theorem b65e_gaugeJet_table_1_3 : ∀ n : Fin 8,
    b65e_gaugeJetQ 1 3 n = b65e_gaugeRhsQ 1 3 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Gauge recursion at pole 1, index 4. -/
theorem b65e_gaugeJet_table_1_4 : ∀ n : Fin 8,
    b65e_gaugeJetQ 1 4 n = b65e_gaugeRhsQ 1 4 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Gauge recursion at pole 1, index 5. -/
theorem b65e_gaugeJet_table_1_5 : ∀ n : Fin 8,
    b65e_gaugeJetQ 1 5 n = b65e_gaugeRhsQ 1 5 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Initial inverse gauge jets at pole 1. -/
theorem b65e_gaugeInvJet_zero_1 : ∀ n : Fin 8,
    b65e_gaugeInvJetQ 1 0 n = if n.val = 0 then 1 else 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Inverse-series recursion at pole 1. -/
theorem b65e_gaugeInvJet_table_1 : ∀ m : Fin 6, ∀ n : Fin 8, m.val ≠ 0 →
    b65e_gaugeInvJetQ 1 m n = b65e_gaugeInvRhsQ 1 m n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- r-coefficient jets at pole 1. -/
theorem b65e_rCoeffJet_table_1 : ∀ m : Fin 6, ∀ n : Fin 8,
    b65e_rCoeffJetQ 1 m n = b65e_convQ (b65e_gaugeInvN 1 m) (b65e_basisInvN 1) n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- q-coefficient jets at pole 1. -/
theorem b65e_qCoeffJet_table_1 : ∀ m : Fin 6, ∀ n : Fin 8,
    b65e_qCoeffJetQ 1 m n = (b65e_convQ (b65e_basisN 1) (b65e_gaugeN 1 m) n)ᵀ := by
  decide +kernel

end HodgeLean.Foundations.Program
