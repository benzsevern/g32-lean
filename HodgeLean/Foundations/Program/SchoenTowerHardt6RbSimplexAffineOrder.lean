import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAffineSimplexEvaluation

/-! Vertexwise order of simplex-affine functions holds throughout the actual simplex hull. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_simplex_affine_order {E : Type*}
    [AddCommGroup E] [Module ℝ E] (s : Finset E) (l u : E → ℝ)
    (hl : ∀ w : stdSimplex ℝ s, l (∑ i, w.val i • i.val) = ∑ i, w.val i * l i.val)
    (hu : ∀ w : stdSimplex ℝ s, u (∑ i, w.val i • i.val) = ∑ i, w.val i * u i.val)
    (hlu : ∀ x ∈ s, l x ≤ u x) :
    ∀ x ∈ convexHull ℝ (↑s : Set E), l x ≤ u x := by
  classical
  intro x hx
  have hr : Set.range (fun i : s => (i.val : E)) = (↑s : Set E) := by
    ext y
    simp only [Set.mem_range, Subtype.exists, exists_prop, exists_eq_right, Finset.mem_coe]
  rw [← hr] at hx
  obtain ⟨w, hw⟩ := (s2v_hardt6rb_convexHull_range_weights (fun i : s => (i.val : E)) x).mp hx
  rw [← hw, hl, hu]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hlu i.val i.property) (w.property.1 i))

end HodgeLean.Foundations.Program
