import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Combination

/-! Finite barycentric coordinates for the ordered prism construction. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_convexHull_range_weights {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] [Fintype ι] (v : ι → E) (x : E) :
    x ∈ convexHull ℝ (Set.range v) ↔
      ∃ w : stdSimplex ℝ ι, (∑ i, w.val i • v i) = x := by
  classical
  constructor
  · intro hx
    rw [convexHull_range_eq_exists_affineCombination] at hx
    obtain ⟨s, c, hc, hc1, hcx⟩ := hx
    let w : ι → ℝ := fun i => if i ∈ s then c i else 0
    have hw1 : (∑ i, w i) = 1 := by
      simpa only [w, Finset.sum_ite_mem, Finset.univ_inter] using hc1
    refine ⟨⟨w, ?_, hw1⟩, ?_⟩
    · intro i
      by_cases hi : i ∈ s
      · simpa only [w, hi, ite_true] using hc i hi
      · simp only [w, hi, ite_false, le_refl]
    · simpa only [Finset.affineCombination_eq_linear_combination s v c hc1,
        w, ite_smul, zero_smul, Finset.sum_ite_mem, Finset.univ_inter] using hcx
  · rintro ⟨w, hw⟩
    exact mem_convexHull_of_exists_fintype w.val v w.property.1 w.property.2
      (fun i => Set.mem_range_self i) hw

theorem s2v_hardt6rb_prism_vertex_range {E : Type*} {m : ℕ}
    (v : Fin (m + 1) → E) (l u : Fin (m + 1) → ℝ) (j : Fin (m + 1)) :
    Set.range (fun o : Option (Fin (m + 1)) =>
      o.elim (v j, u j) (fun i => (v i, if i < j then u i else l i))) =
        ((fun i => (v i, l i)) '' {i | j ≤ i}) ∪
          ((fun i => (v i, u i)) '' {i | i ≤ j}) := by
  ext x
  constructor
  · rintro ⟨o, rfl⟩
    cases o with
    | none => exact Or.inr ⟨j, by simp, rfl⟩
    | some i =>
      by_cases hi : i < j
      · exact Or.inr ⟨i, hi.le, by simp only [Option.elim_some, hi, ite_true]⟩
      · exact Or.inl ⟨i, le_of_not_gt hi, by simp only [Option.elim_some, hi, ite_false]⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · change j ≤ i at hi
      exact ⟨some i, by simp only [Option.elim_some, not_lt.mpr hi, ite_false]⟩
    · by_cases hij : i < j
      · exact ⟨some i, by simp only [Option.elim_some, hij, ite_true]⟩
      · have heq : i = j := le_antisymm hi (le_of_not_gt hij)
        subst i
        exact ⟨none, rfl⟩

end HodgeLean.Foundations.Program
