import HodgeLean.Foundations.Program.SchoenCycleSigmaHeadTail
import Mathlib.Algebra.Group.End

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Independent block permutation families separate into the actual head and tail actions.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
def s2e_block_family_head_tail {b : ℕ} (β : Fin (b + 1) → Type*) :
    (∀ a, Equiv.Perm (β a)) ≃*
      Equiv.Perm (β 0) × (∀ a : Fin b, Equiv.Perm (β a.succ)) where
  toFun ρ := (ρ 0, fun a => ρ a.succ)
  invFun ρ := Fin.cases ρ.1 ρ.2
  left_inv := by
    intro ρ
    funext a
    cases a using Fin.cases with
    | zero => rfl
    | succ a => rfl
  right_inv := by
    intro ρ
    rfl
  map_mul' := fun _ _ => rfl

/-- The actual block action becomes the head action and the tail action under the indexed variable split.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_sigma_head_tail_permutation {b : ℕ} (β : Fin (b + 1) → Type*)
    (ρ : ∀ a, Equiv.Perm (β a)) :
    (s2e_sigma_head_tail β).permCongr (Equiv.Perm.sigmaCongrRight ρ) =
      Equiv.sumCongr (ρ 0) (Equiv.Perm.sigmaCongrRight (fun a : Fin b => ρ a.succ)) := by
  apply Equiv.ext
  intro v
  cases v with
  | inl i => rfl
  | inr v => rfl

end HodgeLean.Foundations.Program
