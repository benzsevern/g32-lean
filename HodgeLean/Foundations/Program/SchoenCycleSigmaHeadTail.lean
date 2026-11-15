import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Group.Equiv.Defs

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The indexed block variables separate into the first block and the retained tail blocks.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
def s2e_sigma_head_tail {b : ℕ} (β : Fin (b + 1) → Type*) :
    (Σ a, β a) ≃ β 0 ⊕ (Σ a : Fin b, β a.succ) where
  toFun v := Fin.cases (motive := fun a => β a → β 0 ⊕ (Σ a : Fin b, β a.succ))
    (fun i => Sum.inl i) (fun a i => Sum.inr ⟨a, i⟩) v.1 v.2
  invFun := Sum.elim (fun i => ⟨0, i⟩) (fun v => ⟨v.1.succ, v.2⟩)
  left_inv := by
    rintro ⟨a, i⟩
    cases a using Fin.cases with
    | zero => rfl
    | succ a => rfl
  right_inv := by
    intro v
    cases v with
    | inl i => rfl
    | inr v => rfl

end HodgeLean.Foundations.Program
