import Mathlib.Logic.Equiv.Fin.Basic

namespace HodgeLean.Foundations.Program

def m1b_pairSlotsLast (k : ℕ) : ((Fin k × Fin 2) ⊕ Fin 2) ≃ Fin (k + 1) × Fin 2 where
  toFun := Sum.elim (fun p => (p.1.castSucc, p.2)) (fun j => (Fin.last k, j))
  invFun p := Fin.lastCases (.inr p.2) (fun i => .inl (i, p.2)) p.1
  left_inv p := by cases p <;> simp
  right_inv p := by
    rcases p with ⟨i, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) i <;> simp

end HodgeLean.Foundations.Program
