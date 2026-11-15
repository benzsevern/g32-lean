import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-! The exact multidegree indexing used in finite-power iteration. -/
open scoped BigOperators

namespace HodgeLean.Foundations.Program

/-- Splitting off the first coordinate identifies total multidegrees with the
binary total-degree index and the remaining multidegree.
Source: Hatcher, Algebraic Topology, §3.2, iteration of the binary Künneth formula. -/
def s4_e1_multidegree_split (h n : ℕ) :
    {d : Fin (h + 1) → ℕ // ∑ i, d i = n} ≃
      Σ p : {p : ℕ × ℕ // p.1 + p.2 = n},
        {d : Fin h → ℕ // ∑ i, d i = p.val.2} where
  toFun d := ⟨⟨(d.val 0, ∑ i, Fin.tail d.val i),
    (Fin.sum_univ_succ d.val).symm.trans d.property⟩, ⟨Fin.tail d.val, rfl⟩⟩
  invFun x := ⟨Fin.cons x.1.val.1 x.2.val, by
    rw [Fin.sum_univ_succ]
    change x.1.val.1 + (∑ i, x.2.val i) = n
    rw [x.2.property]
    exact x.1.property⟩
  left_inv d := by
    apply Subtype.ext
    funext i
    cases i using Fin.cases <;> rfl
  right_inv x := by
    rcases x with ⟨⟨⟨i, j⟩, hp⟩, ⟨d, hd⟩⟩
    dsimp only at hp hd
    subst j
    rfl

#print axioms s4_e1_multidegree_split
end HodgeLean.Foundations.Program
