import Mathlib.Algebra.Order.BigOperators.Group.Finset
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFaceChainMax
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! Nonnegative combinations of nested face indicators have only chain faces as strict superlevel sets. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_chain_superlevel {ι : Type*} [DecidableEq ι]
    (C : Finset (Finset ι))
    (hchain : ∀ S ∈ C, ∀ T ∈ C, S ⊆ T ∨ T ⊆ S)
    (a : Finset ι → ℝ) (ha : ∀ S ∈ C, 0 ≤ a S) (r : ℝ) (hr : 0 ≤ r) :
    ∃ T : Finset ι, (T = ∅ ∨ T ∈ C) ∧
      ∀ i, i ∈ T ↔ r < ∑ S ∈ C, if i ∈ S then a S else 0 := by
  classical
  revert hchain a ha r hr
  induction C using Finset.strongInductionOn with
  | _ C ih =>
    intro hchain a ha r hr
    by_cases hC : C.Nonempty
    · obtain ⟨S, hS, hmax⟩ := s2v_hardt6rb_face_chain_max C hC hchain
      let R := C.erase S
      have hRsub : R ⊆ C := Finset.erase_subset S C
      have hRchain : ∀ U ∈ R, ∀ V ∈ R, U ⊆ V ∨ V ⊆ U :=
        fun U hU V hV => hchain U (hRsub hU) V (hRsub hV)
      have hRa : ∀ U ∈ R, 0 ≤ a U := fun U hU => ha U (hRsub hU)
      have hsum (i : ι) : (∑ U ∈ C, if i ∈ U then a U else 0) =
          (if i ∈ S then a S else 0) + ∑ U ∈ R, if i ∈ U then a U else 0 := by
        rw [← Finset.insert_erase hS, Finset.sum_insert (Finset.notMem_erase S C)]
      have hnonneg (i : ι) : 0 ≤ ∑ U ∈ R, if i ∈ U then a U else 0 := by
        apply Finset.sum_nonneg
        intro U hU
        split_ifs
        · exact hRa U hU
        · exact le_rfl
      have hout (i : ι) (hi : i ∉ S) : (∑ U ∈ R, if i ∈ U then a U else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro U hU
        have hiU : i ∉ U := fun h => hi (hmax U (hRsub hU) h)
        simp only [hiU, ite_false]
      by_cases hSr : r < a S
      · refine ⟨S, Or.inr hS, ?_⟩
        intro i
        rw [hsum i]
        by_cases hi : i ∈ S
        · simp only [hi, ite_true, true_iff]
          linarith [hnonneg i]
        · simp only [hi, ite_false, hout i hi, zero_add, false_iff, not_lt]
          exact hr
      · have hdiff : 0 ≤ r - a S := sub_nonneg.mpr (le_of_not_gt hSr)
        obtain ⟨T, hT, hTi⟩ := ih R (Finset.erase_ssubset hS) hRchain a hRa (r - a S) hdiff
        refine ⟨T, hT.imp_right (fun h => hRsub h), ?_⟩
        intro i
        rw [hTi i, hsum i]
        by_cases hi : i ∈ S
        · simp only [hi, ite_true]
          constructor <;> intro h <;> linarith
        · simp only [hi, ite_false, hout i hi, zero_add]
          constructor <;> intro h <;> linarith
    · have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
      refine ⟨∅, Or.inl rfl, ?_⟩
      intro i
      simp only [Finset.notMem_empty, he, Finset.sum_empty, false_iff, not_lt]
      exact hr

end HodgeLean.Foundations.Program
