import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismWeights
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.Ring

/-! Coverage of a simplex band by its ordered lifted vertex hulls. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_prism_staircase_cover {E : Type*} [AddCommGroup E] [Module ℝ E]
    {m : ℕ} (v : Fin (m + 1) → E) (l u : Fin (m + 1) → ℝ)
    (hlu : ∀ i, l i ≤ u i) (w : stdSimplex ℝ (Fin (m + 1))) {y : ℝ}
    (hylo : (∑ i, w.val i * l i) ≤ y) (hyhi : y ≤ ∑ i, w.val i * u i) :
    ∃ j : Fin (m + 1),
      (∑ i, w.val i • v i, y) ∈ convexHull ℝ
        (((fun i => (v i, l i)) '' {i | j ≤ i}) ∪
          ((fun i => (v i, u i)) '' {i | i ≤ j})) := by
  classical
  have hgap : y - ∑ i, w.val i * l i ≤ ∑ i, w.val i * (u i - l i) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    linarith
  obtain ⟨j, lo, up, hnonneg, hsum, hlo, hup, hheight⟩ :=
    s2v_hardt6rb_prism_staircase_weights w (fun i => u i - l i)
      (fun i => sub_nonneg.mpr (hlu i)) (sub_nonneg.mpr hylo) hgap
  let zlo : Fin (m + 1) → E × ℝ := fun i =>
    if j ≤ i then (v i, l i) else (v j, l j)
  let zup : Fin (m + 1) → E × ℝ := fun i =>
    if i ≤ j then (v i, u i) else (v j, l j)
  have hlo_eq (i) : lo i • zlo i = lo i • (v i, l i) := by
    by_cases hi : j ≤ i
    · simp only [zlo, hi, ite_true]
    · rw [hlo i (lt_of_not_ge hi)]
      simp
  have hup_eq (i) : up i • zup i = up i • (v i, u i) := by
    by_cases hi : i ≤ j
    · simp only [zup, hi, ite_true]
    · rw [hup i (lt_of_not_ge hi)]
      simp
  refine ⟨j, mem_convexHull_of_exists_fintype (Sum.elim lo up) (Sum.elim zlo zup)
    ?_ ?_ ?_ ?_⟩
  · intro i
    cases i with
    | inl i => exact (hnonneg i).1
    | inr i => exact (hnonneg i).2
  · rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.sum_add_distrib]
    simp only [hsum]
    exact w.property.2
  · intro i
    cases i with
    | inl i =>
      dsimp only [Sum.elim_inl, zlo]
      split_ifs with hi
      · exact Or.inl ⟨i, hi, rfl⟩
      · exact Or.inl ⟨j, by simp, rfl⟩
    | inr i =>
      dsimp only [Sum.elim_inr, zup]
      split_ifs with hi
      · exact Or.inr ⟨i, hi, rfl⟩
      · exact Or.inl ⟨j, by simp, rfl⟩
  · rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, hlo_eq, hup_eq]
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.fst_sum]
      change (∑ i, lo i • v i) + (∑ i, up i • v i) = ∑ i, w.val i • v i
      rw [← Finset.sum_add_distrib]
      simp only [← add_smul, hsum]
    · simp only [Prod.snd_add, Prod.snd_sum]
      change (∑ i, lo i * l i) + (∑ i, up i * u i) = y
      have he : (∑ i, lo i * l i) + ∑ i, up i * u i =
          (∑ i, w.val i * l i) + ∑ i, up i * (u i - l i) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← hsum i]
        ring
      rw [he, hheight]
      ring

end HodgeLean.Foundations.Program
