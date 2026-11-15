import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSelection
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Intrinsic

/-! Assembly of marked faces from compatible cell images. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_mark_faces_of_cell_faces {n k : ℕ}
    (A B : Set (EuclideanSpace ℝ (Fin n)))
    (c : Fin k → Set (EuclideanSpace ℝ (Fin n)))
    (hcover : (⋃ i, c i) = A)
    (hcompat : ∀ i, c i ⊆ B ∨ Disjoint (c i) B)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (h : K.space ≃ₜ A)
    (F : Fin k → Finset (Finset (EuclideanSpace ℝ (Fin n))))
    (hF : ∀ i, (↑(F i) : Set _) ⊆ K.faces)
    (hcell : ∀ i, c i = (fun x : K.space => (h x).val) ''
      {x : K.space | ∃ s ∈ F i,
        x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))}) :
    ∃ S : Finset (Finset (EuclideanSpace ℝ (Fin n))),
      (↑S : Set _) ⊆ K.faces ∧
      A ∩ B = (fun x : K.space => (h x).val) ''
        {x : K.space | ∃ s ∈ S,
          x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))} := by
  classical
  obtain ⟨I, hI⟩ := s2v_hardt6rb_select_cells A B c hcover hcompat
  refine ⟨I.biUnion F, ?_, ?_⟩
  · intro s hs
    obtain ⟨i, hi, hsi⟩ := Finset.mem_biUnion.mp hs
    exact hF i hsi
  · rw [hI]
    ext y
    constructor
    · intro hy
      obtain ⟨i, hy⟩ := Set.mem_iUnion.mp hy
      obtain ⟨hi, hyi⟩ := Set.mem_iUnion.mp hy
      rw [hcell i] at hyi
      obtain ⟨x, ⟨s, hs, hxs⟩, hxy⟩ := hyi
      exact ⟨x, ⟨s, Finset.mem_biUnion.mpr ⟨i, hi, hs⟩, hxs⟩, hxy⟩
    · rintro ⟨x, ⟨s, hs, hxs⟩, hxy⟩
      obtain ⟨i, hi, hsi⟩ := Finset.mem_biUnion.mp hs
      refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, ?_⟩⟩
      rw [hcell i]
      exact ⟨x, ⟨s, hsi, hxs⟩, hxy⟩

end HodgeLean.Foundations.Program
