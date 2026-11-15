import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Max
import Mathlib.Order.Fin.Basic
import Mathlib.Basic.Real.Basic

/-! Every closed ordered root interval is the union of its graph levels and intervening adjacent cells. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_ordered_interval_cells {r : ℕ}
    (f : Fin r → ℝ) (hf : StrictMono f) (a b : Fin r) (y : ℝ) :
    (f a ≤ y ∧ y ≤ f b) ↔
      (∃ i, a ≤ i ∧ i ≤ b ∧ y = f i) ∨
      (∃ i j : Fin r, i.val + 1 = j.val ∧ a ≤ i ∧ j ≤ b ∧ f i < y ∧ y < f j) := by
  classical
  constructor
  · intro hy
    by_cases he : ∃ i, y = f i
    · obtain ⟨i, rfl⟩ := he
      exact Or.inl ⟨i, hf.le_iff_le.mp hy.1, hf.le_iff_le.mp hy.2, rfl⟩
    · let S := Finset.univ.filter (fun i => f i < y)
      have ha : a ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        lt_of_le_of_ne hy.1 (fun h => he ⟨a, h.symm⟩)⟩
      obtain ⟨i, hi, hmax⟩ := S.exists_max_image Fin.val ⟨a, ha⟩
      have hiy : f i < y := (Finset.mem_filter.mp hi).2
      have hib : i < b := hf.lt_iff_lt.mp (lt_of_lt_of_le hiy hy.2)
      let j : Fin r := ⟨i.val + 1, by have hb := b.isLt; change i.val < b.val at hib; omega⟩
      have hyj : y < f j := by
        by_contra hn
        have hjy : f j < y := lt_of_le_of_ne (le_of_not_gt hn) (fun h => he ⟨j, h.symm⟩)
        have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjy⟩
        have hm := hmax j hjS
        change i.val + 1 ≤ i.val at hm
        omega
      refine Or.inr ⟨i, j, rfl, ?_, ?_, hiy, hyj⟩
      · exact hmax a ha
      · change i.val + 1 ≤ b.val
        change i.val < b.val at hib
        omega
  · rintro (⟨i, hai, hib, rfl⟩ | ⟨i, j, _, hai, hjb, hiy, hyj⟩)
    · exact ⟨hf.monotone hai, hf.monotone hib⟩
    · exact ⟨(hf.monotone hai).trans hiy.le, hyj.le.trans (hf.monotone hjb)⟩

end HodgeLean.Foundations.Program
