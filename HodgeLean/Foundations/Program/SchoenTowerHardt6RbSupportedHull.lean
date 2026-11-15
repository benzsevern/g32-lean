import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismCoordinates

/-! A finite convex combination belongs to the hull of the vertices with nonzero weights. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_supported_convexHull {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (v : ι → E) (w : stdSimplex ℝ ι) (T : Set E)
    (hT : ∀ i, w.val i ≠ 0 → v i ∈ T) :
    (∑ i, w.val i • v i) ∈ convexHull ℝ T := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show (∑ i, w.val i) ≠ 0 by rw [w.property.2]; exact one_ne_zero)
  let v' : ι → E := fun j => if w.val j = 0 then v i else v j
  apply mem_convexHull_of_exists_fintype w.val v' w.property.1 w.property.2
  · intro j
    by_cases hj : w.val j = 0
    · simpa only [v', hj, ite_true] using hT i hi
    · simpa only [v', hj, ite_false] using hT j hj
  · apply Finset.sum_congr rfl
    intro j hj
    by_cases hz : w.val j = 0 <;> simp only [v', hz, ite_true, ite_false, zero_smul]

end HodgeLean.Foundations.Program
