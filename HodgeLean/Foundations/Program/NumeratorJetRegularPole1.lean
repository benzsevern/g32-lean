import HodgeLean.Foundations.Program.NumeratorJetRegularDefs

/-! # Regular-part coefficient checks at fixed pole 1 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored inverse-power coordinates satisfy their recursion at pole 1, fibre 0. -/
theorem b65e_invPower_rec_1_0 : ∀ l : Fin 5, ∀ m : Fin 8, ∀ c : Fin 6,
    b65e_invPowerLhsQ 1 0 l m c = b65e_invPowerRhsQ 1 0 l m c := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored inverse-power coordinates satisfy their recursion at pole 1, fibre 1. -/
theorem b65e_invPower_rec_1_1 : ∀ l : Fin 5, ∀ m : Fin 8, ∀ c : Fin 6,
    b65e_invPowerLhsQ 1 1 l m c = b65e_invPowerRhsQ 1 1 l m c := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored regular-part jets at pole 1, order 0 satisfy the finite trace formula. -/
theorem b65e_taylorJet_table_1_0 : ∀ n : Fin 8,
    b65e_taylorJetQ 1 0 n = b65e_taylorFixedQ 1 0 n - b65e_taylorMovingQ 1 0 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored regular-part jets at pole 1, order 1 satisfy the finite trace formula. -/
theorem b65e_taylorJet_table_1_1 : ∀ n : Fin 8,
    b65e_taylorJetQ 1 1 n = b65e_taylorFixedQ 1 1 n - b65e_taylorMovingQ 1 1 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored regular-part jets at pole 1, order 2 satisfy the finite trace formula. -/
theorem b65e_taylorJet_table_1_2 : ∀ n : Fin 8,
    b65e_taylorJetQ 1 2 n = b65e_taylorFixedQ 1 2 n - b65e_taylorMovingQ 1 2 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored regular-part jets at pole 1, order 3 satisfy the finite trace formula. -/
theorem b65e_taylorJet_table_1_3 : ∀ n : Fin 8,
    b65e_taylorJetQ 1 3 n = b65e_taylorFixedQ 1 3 n - b65e_taylorMovingQ 1 3 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored regular-part jets at pole 1, order 4 satisfy the finite trace formula. -/
theorem b65e_taylorJet_table_1_4 : ∀ n : Fin 8,
    b65e_taylorJetQ 1 4 n = b65e_taylorFixedQ 1 4 n - b65e_taylorMovingQ 1 4 n := by
  decide +kernel

end HodgeLean.Foundations.Program
