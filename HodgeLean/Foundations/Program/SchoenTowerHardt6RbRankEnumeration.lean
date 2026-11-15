import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin

/-! Finite geometric cell labels have an enumeration placing every smaller rank first. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_rank_enumeration {ι : Type*} [Fintype ι] (rank : ι → ℕ) :
    ∃ e : Fin (Fintype.card ι) ≃ ι,
      ∀ i j, rank (e i) < rank (e j) → i < j := by
  classical
  let q := Fintype.equivFin ι
  let key : ι → ℕ := fun i => rank i * Fintype.card ι + (q i).val
  have hmod (i : ι) : key i % Fintype.card ι = (q i).val := by
    simp only [key, Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_eq_of_lt (q i).isLt]
  have hinj : Function.Injective key := by
    intro i j hij
    apply q.injective
    apply Fin.ext
    rw [← hmod i, ← hmod j, hij]
  have hkey {i j : ι} (h : rank i < rank j) : key i < key j := by
    have hm := Nat.mul_le_mul_right (Fintype.card ι) (Nat.succ_le_of_lt h)
    have hi : key i < (rank i + 1) * Fintype.card ι := by
      dsimp only [key]
      rw [Nat.add_mul, one_mul]
      exact Nat.add_lt_add_left (q i).isLt _
    exact hi.trans_le (hm.trans (Nat.le_add_right _ _))
  letI : LinearOrder ι := LinearOrder.lift' key hinj
  let e := Fintype.orderIsoFinOfCardEq ι rfl
  refine ⟨e.toEquiv, ?_⟩
  intro i j hij
  have he : e i < e j := hkey hij
  exact e.lt_iff_lt.mp he

end HodgeLean.Foundations.Program
