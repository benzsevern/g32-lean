import HodgeLean.Foundations.Program.NumeratorJetGaugeDefs

/-! # Gauge and Laurent coefficient checks at fixed pole 3 -/

namespace HodgeLean.Foundations.Program
open Matrix

set_option maxHeartbeats 400000 in
/-- Conjugated regular-part jets at pole 3. -/
theorem b65e_conjJet_table_3 : ∀ l : Fin 5, ∀ n : Fin 8,
    b65e_conjJetQ 3 l n =
      b65e_convQ (b65e_basisInvN 3) (b65e_convQ (b65e_taylorN 3 l) (b65e_basisN 3)) n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Initial gauge jets at pole 3. -/
theorem b65e_gaugeJet_zero_3 : ∀ n : Fin 8,
    b65e_gaugeJetQ 3 0 n = if n.val = 0 then 1 else 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Gauge recursion at pole 3, index 1. -/
theorem b65e_gaugeJet_table_3_1 : ∀ n : Fin 8,
    b65e_gaugeJetQ 3 1 n = b65e_gaugeRhsQ 3 1 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Gauge recursion at pole 3, index 2. -/
theorem b65e_gaugeJet_table_3_2 : ∀ n : Fin 8,
    b65e_gaugeJetQ 3 2 n = b65e_gaugeRhsQ 3 2 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Gauge recursion at pole 3, index 3. -/
theorem b65e_gaugeJet_table_3_3 : ∀ n : Fin 8,
    b65e_gaugeJetQ 3 3 n = b65e_gaugeRhsQ 3 3 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Gauge recursion at pole 3, index 4. -/
theorem b65e_gaugeJet_table_3_4 : ∀ n : Fin 8,
    b65e_gaugeJetQ 3 4 n = b65e_gaugeRhsQ 3 4 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Gauge recursion at pole 3, index 5. -/
theorem b65e_gaugeJet_table_3_5 : ∀ n : Fin 8,
    b65e_gaugeJetQ 3 5 n = b65e_gaugeRhsQ 3 5 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Initial inverse gauge jets at pole 3. -/
theorem b65e_gaugeInvJet_zero_3 : ∀ n : Fin 8,
    b65e_gaugeInvJetQ 3 0 n = if n.val = 0 then 1 else 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Inverse-series recursion at pole 3. -/
theorem b65e_gaugeInvJet_table_3 : ∀ m : Fin 6, ∀ n : Fin 8, m.val ≠ 0 →
    b65e_gaugeInvJetQ 3 m n = b65e_gaugeInvRhsQ 3 m n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- r-coefficient jets at pole 3. -/
theorem b65e_rCoeffJet_table_3 : ∀ m : Fin 6, ∀ n : Fin 8,
    b65e_rCoeffJetQ 3 m n = b65e_convQ (b65e_gaugeInvN 3 m) (b65e_basisInvN 3) n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- q-coefficient jets at pole 3. -/
theorem b65e_qCoeffJet_table_3 : ∀ m : Fin 6, ∀ n : Fin 8,
    b65e_qCoeffJetQ 3 m n = (b65e_convQ (b65e_basisN 3) (b65e_gaugeN 3 m) n)ᵀ := by
  decide +kernel

end HodgeLean.Foundations.Program
