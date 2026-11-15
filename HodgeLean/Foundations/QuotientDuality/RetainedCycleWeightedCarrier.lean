import HodgeLean.Foundations.QuotientDuality.ProperCycleCollection

/-! Transport of finite weighted classes from the active carrier to the full family carrier. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
open scoped BigOperators Classical
namespace HodgeLean.Foundations.QuotientDuality

/-- Enlarging the active carrier retains every summand, including zero weights. -/
lemma retained_weighted_active_to_full
    {I : Type} [Fintype I] (Y : TopCat.{0}) (n : ℕ)
    (S : I → Set Y) (q : I → ℚ)
    (a : ∀ i, CohomologyWithSupport ℚ Y (S i) n)
    (A : Set Y) (hA : A ⊆ ⋃ i, ⋃ (_ : q i ≠ 0), S i)
    (b : CohomologyWithSupport ℚ Y A n)
    (hb : enlargeSupport ℚ Y hA n b =
      SupportedClasses.weightedSum Y n S (⋃ i, ⋃ (_ : q i ≠ 0), S i) q
        (fun i hi z hz => Set.mem_iUnion₂.mpr ⟨i, hi, hz⟩) a) :
    enlargeSupport ℚ Y
      (hA.trans (by
        intro z hz
        obtain ⟨i, _, hi⟩ := Set.mem_iUnion₂.mp hz
        exact Set.mem_iUnion.mpr ⟨i, hi⟩)) n b =
      ∑ i, q i • enlargeSupport ℚ Y (Set.subset_iUnion S i) n (a i) := by
  let hT : (⋃ i, ⋃ (_ : q i ≠ 0), S i) ⊆ ⋃ i, S i := by
    intro z hz
    obtain ⟨i, _, hi⟩ := Set.mem_iUnion₂.mp hz
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hc : enlargeSupport ℚ Y (hA.trans hT) n b =
      enlargeSupport ℚ Y hT n (enlargeSupport ℚ Y hA n b) := by
    unfold enlargeSupport
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
    rfl
  rw [hc, hb, properCycle_enlarge_weightedSum]
  unfold SupportedClasses.weightedSum
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : q i ≠ 0
  · rw [dite_eq_left hi]
  · rw [dite_eq_right hi, not_ne_iff.mp hi, zero_smul]

end HodgeLean.Foundations.QuotientDuality
