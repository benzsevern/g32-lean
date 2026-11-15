import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAffineSimplexEvaluation

/-! Ambient affine interpolants agree on every finite hull supported on shared vertex values. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_affine_hull_agreement {E : Type*}
    [AddCommGroup E] [Module ℝ E] (s : Finset E) (L M : E →ᵃ[ℝ] ℝ)
    (h : ∀ x ∈ s, L x = M x) : Set.EqOn L M (convexHull ℝ (↑s : Set E)) := by
  classical
  intro x hx
  have hr : Set.range (fun i : s => (i.val : E)) = (↑s : Set E) := by
    ext y
    simp only [Set.mem_range, Subtype.exists, exists_prop, exists_eq_right, Finset.mem_coe]
  rw [← hr] at hx
  obtain ⟨w, hw⟩ := (s2v_hardt6rb_convexHull_range_weights (fun i : s => (i.val : E)) x).mp hx
  rw [← hw, s2v_hardt6rb_affine_simplex_evaluation, s2v_hardt6rb_affine_simplex_evaluation]
  exact Finset.sum_congr rfl (fun i _ => by rw [h i.val i.property])

end HodgeLean.Foundations.Program
