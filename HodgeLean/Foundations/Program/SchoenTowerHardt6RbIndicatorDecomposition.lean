import HodgeLean.Foundations.Program.SchoenTowerHardt6RbChainSuperlevel

/-! Finite nested-indicator decomposition of nonnegative vertex coordinates. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_indicator_chain_decomposition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∃ C : Finset (Finset ι), ∃ a : Finset ι → ℝ,
      (∀ T ∈ C, T.Nonempty) ∧
      (∀ S ∈ C, ∀ T ∈ C, S ⊆ T ∨ T ⊆ S) ∧
      (∀ T ∈ C, 0 ≤ a T) ∧
      (∀ T ∈ C, ∀ i ∈ T, 0 < w i) ∧
      (∀ i, w i = ∑ T ∈ C, if i ∈ T then a T else 0) := by
  classical
  generalize hcard : (Finset.univ.filter (fun i => 0 < w i)).card = n
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
    let S := Finset.univ.filter (fun i => 0 < w i)
    by_cases hS : S.Nonempty
    · obtain ⟨j, hj, hmin⟩ := S.exists_min_image w hS
      have hd : 0 < w j := (Finset.mem_filter.mp hj).2
      let w' : ι → ℝ := fun i => if 0 < w i then w i - w j else 0
      have hw' : ∀ i, 0 ≤ w' i := by
        intro i
        by_cases hi : 0 < w i
        · simpa only [w', hi, ite_true] using
            sub_nonneg.mpr (hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))
        · simp only [w', hi, ite_false, le_refl]
      have hsupport (i : ι) (hi : 0 < w' i) : 0 < w i := by
        by_contra hn
        simp only [w', hn, ite_false, lt_self_iff_false] at hi
      have hwj : w' j = 0 := by simp only [w', hd, ite_true, sub_self]
      have hsub : Finset.univ.filter (fun i => 0 < w' i) ⊆ S.erase j := by
        intro i hi
        have hwi := (Finset.mem_filter.mp hi).2
        have hij : i ≠ j := by intro he; subst i; rw [hwj] at hwi; exact lt_irrefl _ hwi
        exact Finset.mem_erase.mpr ⟨hij,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsupport i hwi⟩⟩
      have hlt : (Finset.univ.filter (fun i => 0 < w' i)).card < n := by
        rw [← hcard]
        exact lt_of_le_of_lt (Finset.card_le_card hsub) (Finset.card_erase_lt_of_mem hj)
      obtain ⟨C, a, hneC, hchainC, haC, hsupC, hrepC⟩ :=
        ih _ hlt w' hw' rfl
      have hCS : ∀ T ∈ C, T ⊆ S := by
        intro T hT i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsupport i (hsupC T hT i hi)⟩
      have hnot : S ∉ C := by
        intro hSC
        have he := hsupC S hSC j hj
        rw [hwj] at he
        exact lt_irrefl _ he
      let a' : Finset ι → ℝ := fun T => if T = S then w j else a T
      refine ⟨insert S C, a', ?_, ?_, ?_, ?_, ?_⟩
      · intro T hT
        rcases Finset.mem_insert.mp hT with rfl | hT
        · exact hS
        · exact hneC T hT
      · intro T hT U hU
        rcases Finset.mem_insert.mp hT with rfl | hT <;>
          rcases Finset.mem_insert.mp hU with rfl | hU
        · exact Or.inl Finset.Subset.rfl
        · exact Or.inr (hCS U hU)
        · exact Or.inl (hCS T hT)
        · exact hchainC T hT U hU
      · intro T hT
        by_cases hTS : T = S
        · simpa only [a', hTS, ite_true] using hd.le
        · have hTC : T ∈ C := (Finset.mem_insert.mp hT).resolve_left hTS
          simpa only [a', hTS, ite_false] using haC T hTC
      · intro T hT i hi
        rcases Finset.mem_insert.mp hT with rfl | hT
        · exact (Finset.mem_filter.mp hi).2
        · exact hsupport i (hsupC T hT i hi)
      · intro i
        rw [Finset.sum_insert hnot]
        have hsuma : (∑ T ∈ C, if i ∈ T then a' T else 0) =
            ∑ T ∈ C, if i ∈ T then a T else 0 := by
          apply Finset.sum_congr rfl
          intro T hT
          have hTS : T ≠ S := fun he => hnot (he ▸ hT)
          simp only [a', hTS, ite_false]
        rw [hsuma, ← hrepC i]
        by_cases hi : 0 < w i
        · have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
          simp only [a', if_pos rfl, hiS, ite_true, w', hi]
          linarith
        · have hiS : i ∉ S := fun h => hi (Finset.mem_filter.mp h).2
          simp only [hiS, ite_false, w', hi, zero_add]
          exact le_antisymm (le_of_not_gt hi) (hw i)
    · refine ⟨∅, (fun _ => 0), (by simp), (by simp), (by simp), (by simp), ?_⟩
      intro i
      have hi : ¬ 0 < w i := fun h => hS ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
      simpa only [Finset.sum_empty] using le_antisymm (le_of_not_gt hi) (hw i)

end HodgeLean.Foundations.Program
