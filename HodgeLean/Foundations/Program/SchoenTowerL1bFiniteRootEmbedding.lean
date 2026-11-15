import Mathlib.Data.Set.Finite.Range
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

noncomputable section
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Distinct roots of an ordered product occupy distinct ordered positions. -/
theorem s2v_l1b_finite_root_embedding
    {K ι : Type*} [Field K] (n : ℕ) (z : Fin n → K)
    (a : ι → K) (ha : Function.Injective a)
    (hz : ∀ t, (∏ i, (z i - a t)) = 0) :
    ∃ f : ι ↪ Fin n, ∀ t, z (f t) = a t := by
  classical
  have hpos (t : ι) : ∃ i, z i = a t := by
    obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp (hz t)
    exact ⟨i, sub_eq_zero.mp hi⟩
  choose f hf using hpos
  exact ⟨⟨f, fun i j hij => ha ((hf i).symm.trans ((congrArg z hij).trans (hf j)))⟩, hf⟩

/-- A finite family of distinct values extends along any embedding into a finite index type. -/
theorem s2v_l1b_extend_finite_values
    {K ι κ : Type*} [Infinite K] [Fintype ι] [Fintype κ]
    (f : ι ↪ κ) (a : ι → K) (ha : Function.Injective a) :
    ∃ b : κ → K, Function.Injective b ∧ ∀ t, b (f t) = a t := by
  classical
  let V : Set K := (Set.range a)ᶜ
  have hV : V.Infinite := (Set.finite_range a).infinite_compl
  letI : Infinite V := hV.to_subtype
  let g : κ ↪ V :=
    (Fintype.equivFin κ).toEmbedding.trans
      ((⟨Fin.val, Fin.val_injective⟩ : Fin (Fintype.card κ) ↪ ℕ).trans
        (Infinite.natEmbedding V))
  let b (i : κ) : K := if hi : ∃ t, f t = i then a hi.choose else (g i).val
  have hb (t : ι) : b (f t) = a t := by
    have ht : ∃ s, f s = f t := ⟨t, rfl⟩
    simp only [b, dif_pos ht]
    exact congrArg a (f.injective ht.choose_spec)
  refine ⟨b, ?_, hb⟩
  intro i j hij
  by_cases hi : ∃ t, f t = i
  · obtain ⟨t, rfl⟩ := hi
    rw [hb] at hij
    by_cases hj : ∃ s, f s = j
    · obtain ⟨s, rfl⟩ := hj
      rw [hb] at hij
      exact congrArg f (ha hij)
    · have hnot := (g j).property
      apply False.elim
      apply hnot
      exact ⟨t, hij.trans (by simp only [b, dif_neg hj])⟩
  · by_cases hj : ∃ s, f s = j
    · obtain ⟨s, rfl⟩ := hj
      rw [hb] at hij
      have hnot := (g i).property
      exact False.elim (hnot ⟨s, hij.symm.trans (by simp only [b, dif_neg hi])⟩)
    · apply g.injective
      apply Subtype.ext
      simpa only [b, dif_neg hi, dif_neg hj] using hij

end HodgeLean.Foundations.Program
