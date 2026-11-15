import HodgeLean.Foundations.Program.NumeratorJetNumeratorDefs

/-! # Rational checks of the moving-power coordinates and the branch-polynomial jets -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- At power zero the moving-power coordinates are those of the constant `1`. -/
theorem b65e_TcQ_zero_table : ∀ e : Fin 2, ∀ n : Fin 8, ∀ c : Fin 6,
    b65e_TcQ e 0 n c = if n.val = 0 then b65e_oneCoordQ c else 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored moving-power coordinates satisfy the binomial recursion. -/
theorem b65e_TcQ_step_table : ∀ e : Fin 2, ∀ m : Fin 12, ∀ n : Fin 8, ∀ c : Fin 6,
    b65e_TcQ e m.succ n c = b65e_TcStepQ e m.val n.val c := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The order-zero symmetric function is `1`. -/
theorem b65e_esymQ_zero_table : ∀ n : Fin 8, b65e_esymQ 0 n = if n.val = 0 then 1 else 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored symmetric-function jets satisfy the Newton identities. -/
theorem b65e_esymQ_newton_table : ∀ k : Fin 12, ∀ n : Fin 8,
    ((k.val + 1 : ℕ) : ℚ) * b65e_esymQ k.succ n = b65e_newtonQ (k.val + 1) n.val := by
  decide +kernel

end HodgeLean.Foundations.Program
