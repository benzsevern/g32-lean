import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFaceSelection

/-! Finite families of actual cell face selections retain every compatible target mark. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_finite_cell_mark_selection {n : ℕ} {ι : Type*} [Fintype ι]
    (A B : Set (EuclideanSpace ℝ (Fin n))) (c : ι → Set (EuclideanSpace ℝ (Fin n)))
    (hcover : (⋃ i, c i) = A) (hcompat : ∀ i, c i ⊆ B ∨ Disjoint (c i) B)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) (h : K.space ≃ₜ A)
    (hcell : ∀ i, ∃ F : Finset (Finset (EuclideanSpace ℝ (Fin n))),
      (↑F : Set _) ⊆ K.faces ∧ c i = (fun x : K.space => (h x).val) ''
        {x : K.space | ∃ s ∈ F, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))}) :
    ∃ S : Finset (Finset (EuclideanSpace ℝ (Fin n))), (↑S : Set _) ⊆ K.faces ∧
      A ∩ B = (fun x : K.space => (h x).val) ''
        {x : K.space | ∃ s ∈ S, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))} := by
  classical
  let e := (Fintype.equivFin ι).symm
  have hcover' : (⋃ j, c (e j)) = A := by
    rw [← hcover]
    ext x
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨j, hj⟩ => ⟨e j, hj⟩,
      fun ⟨i, hi⟩ => ⟨e.symm i, by simpa only [e.apply_symm_apply] using hi⟩⟩
  choose F hF heq using fun j => hcell (e j)
  exact s2v_hardt6rb_mark_faces_of_cell_faces A B (fun j => c (e j)) hcover'
    (fun j => hcompat (e j)) K h F hF heq

end HodgeLean.Foundations.Program
