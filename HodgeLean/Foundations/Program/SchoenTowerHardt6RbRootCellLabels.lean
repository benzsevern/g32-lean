import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOrderedCellLabels
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin

/-! Finite graph and adjacent-band labels and their actual endpoint indices. -/
namespace HodgeLean.Foundations.Program

abbrev s2v_hardt6rb_RootLabel (r : ℕ) :=
  Fin r ⊕ {p : Fin r × Fin r // p.1.val + 1 = p.2.val}

def s2v_hardt6rb_rootLabelLower {r : ℕ} : s2v_hardt6rb_RootLabel r → Fin r
  | .inl i => i
  | .inr p => p.val.1

def s2v_hardt6rb_rootLabelUpper {r : ℕ} : s2v_hardt6rb_RootLabel r → Fin r
  | .inl i => i
  | .inr p => p.val.2

def s2v_hardt6rb_rootLabelStep {r : ℕ} : s2v_hardt6rb_RootLabel r → ℕ
  | .inl _ => 0
  | .inr _ => 1

theorem s2v_hardt6rb_root_label_endpoints {r : ℕ} (a : s2v_hardt6rb_RootLabel r) :
    s2v_hardt6rb_rootLabelLower a ≤ s2v_hardt6rb_rootLabelUpper a ∧
      (s2v_hardt6rb_rootLabelUpper a).val =
        (s2v_hardt6rb_rootLabelLower a).val + s2v_hardt6rb_rootLabelStep a ∧
      s2v_hardt6rb_rootLabelStep a ≤ 1 := by
  cases a with
  | inl i => exact ⟨le_rfl, rfl, Nat.zero_le 1⟩
  | inr p =>
    refine ⟨?_, p.property.symm, le_rfl⟩
    change p.val.1.val ≤ p.val.2.val
    have hp := p.property
    omega

end HodgeLean.Foundations.Program
