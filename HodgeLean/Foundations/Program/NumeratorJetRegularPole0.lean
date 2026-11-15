import HodgeLean.Foundations.Program.NumeratorJetRegularDefs

/-! # Regular-part coefficient checks at fixed pole 0 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored inverse-power coordinates satisfy their recursion at pole 0, fibre 0. -/
theorem b65e_invPower_rec_0_0 : ∀ l : Fin 5, ∀ m : Fin 8, ∀ c : Fin 6,
    b65e_invPowerLhsQ 0 0 l m c = b65e_invPowerRhsQ 0 0 l m c := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored inverse-power coordinates satisfy their recursion at pole 0, fibre 1. -/
theorem b65e_invPower_rec_0_1 : ∀ l : Fin 5, ∀ m : Fin 8, ∀ c : Fin 6,
    b65e_invPowerLhsQ 0 1 l m c = b65e_invPowerRhsQ 0 1 l m c := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored regular-part jets at pole 0, order 0 satisfy the finite trace formula. -/
theorem b65e_taylorJet_table_0_0 : ∀ n : Fin 8,
    b65e_taylorJetQ 0 0 n = b65e_taylorFixedQ 0 0 n - b65e_taylorMovingQ 0 0 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored regular-part jets at pole 0, order 1 satisfy the finite trace formula. -/
theorem b65e_taylorJet_table_0_1 : ∀ n : Fin 8,
    b65e_taylorJetQ 0 1 n = b65e_taylorFixedQ 0 1 n - b65e_taylorMovingQ 0 1 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored regular-part jets at pole 0, order 2 satisfy the finite trace formula. -/
theorem b65e_taylorJet_table_0_2 : ∀ n : Fin 8,
    b65e_taylorJetQ 0 2 n = b65e_taylorFixedQ 0 2 n - b65e_taylorMovingQ 0 2 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored regular-part jets at pole 0, order 3 satisfy the finite trace formula. -/
theorem b65e_taylorJet_table_0_3 : ∀ n : Fin 8,
    b65e_taylorJetQ 0 3 n = b65e_taylorFixedQ 0 3 n - b65e_taylorMovingQ 0 3 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored regular-part jets at pole 0, order 4 satisfy the finite trace formula. -/
theorem b65e_taylorJet_table_0_4 : ∀ n : Fin 8,
    b65e_taylorJetQ 0 4 n = b65e_taylorFixedQ 0 4 n - b65e_taylorMovingQ 0 4 n := by
  decide +kernel

end HodgeLean.Foundations.Program
