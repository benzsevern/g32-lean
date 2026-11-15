import HodgeLean.Foundations.Program.SchoenTowerHardt6RbVerticalIndependence

/-! Ordered lifted vertex hulls are simplices, including collapsed pivots. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_prism_staircase_independent {E : Type*}
    [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (v : Fin (m + 1) → E) (hv : AffineIndependent ℝ v)
    (l u : Fin (m + 1) → ℝ) (j : Fin (m + 1)) :
    AffineIndependent ℝ (fun x : ↥(
      (((fun i => (v i, l i)) '' {i | j ≤ i}) ∪
        ((fun i => (v i, u i)) '' {i | i ≤ j}) : Set (E × ℝ))) => (x : E × ℝ)) := by
  let heights : Fin (m + 1) → ℝ := fun i => if i < j then u i else l i
  let q : Fin (m + 1) → E × ℝ := fun i => (v i, heights i)
  by_cases hz : u j = l j
  · have hq : AffineIndependent ℝ q := by
      apply AffineIndependent.of_comp (AffineMap.fst : E × ℝ →ᵃ[ℝ] E)
      exact hv
    apply hq.range.mono
    rintro x (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · change j ≤ i at hi
      exact ⟨i, by simp only [q, heights, not_lt.mpr hi, ite_false]⟩
    · by_cases hij : i < j
      · exact ⟨i, by simp only [q, heights, hij, ite_true]⟩
      · have heq : i = j := le_antisymm hi (le_of_not_gt hij)
        subst i
        exact ⟨j, by simp only [q, heights, lt_self_iff_false, ite_false, hz]⟩
  · have hi := s2v_hardt6rb_vertical_vertex_independent v hv heights j (u j)
      (by simpa only [heights, lt_self_iff_false, ite_false] using hz)
    apply hi.range.mono
    rintro x (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · change j ≤ i at hi
      exact ⟨some i, by simp only [Option.elim_some, heights, not_lt.mpr hi, ite_false]⟩
    · by_cases hij : i < j
      · exact ⟨some i, by simp only [Option.elim_some, heights, hij, ite_true]⟩
      · have heq : i = j := le_antisymm hi (le_of_not_gt hij)
        subst i
        exact ⟨none, rfl⟩

end HodgeLean.Foundations.Program
