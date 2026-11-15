import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGeometricRestriction

/-! Projection of every lifted face stays inside its actual base simplex. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_prism_face_projection {E : Type*}
    [AddCommGroup E] [Module ℝ E] [LinearOrder E]
    (s : Finset E) (l u : E → ℝ) (j : s) (r : Finset (E × ℝ))
    (hr : (↑r : Set (E × ℝ)) ⊆
      (((fun i : s => (i.val, l i.val)) '' {i | j ≤ i}) ∪
        ((fun i : s => (i.val, u i.val)) '' {i | i ≤ j}))) :
    convexHull ℝ (↑r : Set (E × ℝ)) ⊆
      Prod.fst ⁻¹' convexHull ℝ (↑s : Set E) := by
  apply convexHull_min
  · intro p hp
    rcases hr hp with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;>
      exact subset_convexHull ℝ _ i.property
  · exact (convex_convexHull ℝ _).linear_preimage (LinearMap.fst ℝ E ℝ)

end HodgeLean.Foundations.Program
