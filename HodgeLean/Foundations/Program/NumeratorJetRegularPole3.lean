import HodgeLean.Foundations.Program.NumeratorJetRegularDefs

/-! # Regular-part coefficient checks at fixed pole 3 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored inverse-power coordinates satisfy their recursion at pole 3, fibre 0. -/
theorem b65e_invPower_rec_3_0 : ∀ l : Fin 5, ∀ m : Fin 8, ∀ c : Fin 6,
    b65e_invPowerLhsQ 3 0 l m c = b65e_invPowerRhsQ 3 0 l m c := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored inverse-power coordinates satisfy their recursion at pole 3, fibre 1. -/
theorem b65e_invPower_rec_3_1 : ∀ l : Fin 5, ∀ m : Fin 8, ∀ c : Fin 6,
    b65e_invPowerLhsQ 3 1 l m c = b65e_invPowerRhsQ 3 1 l m c := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored regular-part jets at pole 3, order 0 satisfy the finite trace formula. -/
theorem b65e_taylorJet_table_3_0 : ∀ n : Fin 8,
    b65e_taylorJetQ 3 0 n = b65e_taylorFixedQ 3 0 n - b65e_taylorMovingQ 3 0 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored regular-part jets at pole 3, order 1 satisfy the finite trace formula. -/
theorem b65e_taylorJet_table_3_1 : ∀ n : Fin 8,
    b65e_taylorJetQ 3 1 n = b65e_taylorFixedQ 3 1 n - b65e_taylorMovingQ 3 1 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored regular-part jets at pole 3, order 2 satisfy the finite trace formula. -/
theorem b65e_taylorJet_table_3_2 : ∀ n : Fin 8,
    b65e_taylorJetQ 3 2 n = b65e_taylorFixedQ 3 2 n - b65e_taylorMovingQ 3 2 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored regular-part jets at pole 3, order 3 satisfy the finite trace formula. -/
theorem b65e_taylorJet_table_3_3 : ∀ n : Fin 8,
    b65e_taylorJetQ 3 3 n = b65e_taylorFixedQ 3 3 n - b65e_taylorMovingQ 3 3 n := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored regular-part jets at pole 3, order 4 satisfy the finite trace formula. -/
theorem b65e_taylorJet_table_3_4 : ∀ n : Fin 8,
    b65e_taylorJetQ 3 4 n = b65e_taylorFixedQ 3 4 n - b65e_taylorMovingQ 3 4 n := by
  decide +kernel

end HodgeLean.Foundations.Program
