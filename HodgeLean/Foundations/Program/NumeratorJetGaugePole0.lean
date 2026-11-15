import HodgeLean.Foundations.Program.NumeratorJetGaugeDefs

/-! # Gauge and Laurent coefficient checks at fixed pole 0 -/

namespace HodgeLean.Foundations.Program
open Matrix

set_option maxHeartbeats 400000 in
/-- Conjugated regular-part jets at pole 0. -/
theorem b65e_conjJet_table_0 : ∀ l : Fin 5, ∀ n : Fin 8,
    b65e_conjJetQ 0 l n =
      b65e_convQ (b65e_basisInvN 0) (b65e_convQ (b65e_taylorN 0 l) (b65e_basisN 0)) n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Initial gauge jets at pole 0. -/
theorem b65e_gaugeJet_zero_0 : ∀ n : Fin 8,
    b65e_gaugeJetQ 0 0 n = if n.val = 0 then 1 else 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Gauge recursion at pole 0, index 1. -/
theorem b65e_gaugeJet_table_0_1 : ∀ n : Fin 8,
    b65e_gaugeJetQ 0 1 n = b65e_gaugeRhsQ 0 1 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Gauge recursion at pole 0, index 2. -/
theorem b65e_gaugeJet_table_0_2 : ∀ n : Fin 8,
    b65e_gaugeJetQ 0 2 n = b65e_gaugeRhsQ 0 2 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Gauge recursion at pole 0, index 3. -/
theorem b65e_gaugeJet_table_0_3 : ∀ n : Fin 8,
    b65e_gaugeJetQ 0 3 n = b65e_gaugeRhsQ 0 3 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Gauge recursion at pole 0, index 4. -/
theorem b65e_gaugeJet_table_0_4 : ∀ n : Fin 8,
    b65e_gaugeJetQ 0 4 n = b65e_gaugeRhsQ 0 4 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Gauge recursion at pole 0, index 5. -/
theorem b65e_gaugeJet_table_0_5 : ∀ n : Fin 8,
    b65e_gaugeJetQ 0 5 n = b65e_gaugeRhsQ 0 5 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Initial inverse gauge jets at pole 0. -/
theorem b65e_gaugeInvJet_zero_0 : ∀ n : Fin 8,
    b65e_gaugeInvJetQ 0 0 n = if n.val = 0 then 1 else 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Inverse-series recursion at pole 0. -/
theorem b65e_gaugeInvJet_table_0 : ∀ m : Fin 6, ∀ n : Fin 8, m.val ≠ 0 →
    b65e_gaugeInvJetQ 0 m n = b65e_gaugeInvRhsQ 0 m n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- r-coefficient jets at pole 0. -/
theorem b65e_rCoeffJet_table_0 : ∀ m : Fin 6, ∀ n : Fin 8,
    b65e_rCoeffJetQ 0 m n = b65e_convQ (b65e_gaugeInvN 0 m) (b65e_basisInvN 0) n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- q-coefficient jets at pole 0. -/
theorem b65e_qCoeffJet_table_0 : ∀ m : Fin 6, ∀ n : Fin 8,
    b65e_qCoeffJetQ 0 m n = (b65e_convQ (b65e_basisN 0) (b65e_gaugeN 0 m) n)ᵀ := by
  decide +kernel

end HodgeLean.Foundations.Program
