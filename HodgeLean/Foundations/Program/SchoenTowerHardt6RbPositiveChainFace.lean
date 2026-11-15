import HodgeLean.Foundations.Program.SchoenTowerHardt6RbChainSuperlevel

/-! Every face with positive coefficient is detected by a strict level gap. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_positive_chain_face_superlevel {ι : Type*} [DecidableEq ι]
    (C : Finset (Finset ι))
    (hchain : ∀ S ∈ C, ∀ T ∈ C, S ⊆ T ∨ T ⊆ S)
    (a : Finset ι → ℝ) (ha : ∀ S ∈ C, 0 ≤ a S)
    (T : Finset ι) (hT : T ∈ C) (haT : 0 < a T) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ i, i ∈ T ↔ r < ∑ S ∈ C, if i ∈ S then a S else 0 := by
  classical
  let R := C.erase T
  let r : ℝ := ∑ U ∈ R, if T ⊆ U then a U else 0
  have hRa : ∀ U ∈ R, 0 ≤ a U := fun U hU => ha U (Finset.mem_of_mem_erase hU)
  have hr : 0 ≤ r := by
    apply Finset.sum_nonneg
    intro U hU
    split_ifs
    · exact hRa U hU
    · exact le_rfl
  have hsum (i : ι) : (∑ U ∈ C, if i ∈ U then a U else 0) =
      (if i ∈ T then a T else 0) + ∑ U ∈ R, if i ∈ U then a U else 0 := by
    rw [← Finset.insert_erase hT, Finset.sum_insert (Finset.notMem_erase T C)]
  refine ⟨r, hr, ?_⟩
  intro i
  rw [hsum i]
  by_cases hi : i ∈ T
  · have hle : r ≤ ∑ U ∈ R, if i ∈ U then a U else 0 := by
      apply Finset.sum_le_sum
      intro U hU
      by_cases hTU : T ⊆ U
      · simp only [hTU, ite_true, hTU hi, le_refl]
      · simp only [hTU, ite_false]
        split_ifs
        · exact hRa U hU
        · exact le_rfl
    simp only [hi, ite_true, true_iff]
    linarith
  · have hle : (∑ U ∈ R, if i ∈ U then a U else 0) ≤ r := by
      apply Finset.sum_le_sum
      intro U hU
      by_cases hiU : i ∈ U
      · have hTU : T ⊆ U := by
          rcases hchain T hT U (Finset.mem_of_mem_erase hU) with h | h
          · exact h
          · exact False.elim (hi (h hiU))
        simp only [hiU, hTU, ite_true, le_refl]
      · simp only [hiU, ite_false]
        split_ifs
        · exact hRa U hU
        · exact le_rfl
    simp only [hi, ite_false, zero_add, false_iff, not_lt]
    exact hle

end HodgeLean.Foundations.Program
