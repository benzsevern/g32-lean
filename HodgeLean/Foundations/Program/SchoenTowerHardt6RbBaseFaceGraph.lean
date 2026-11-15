import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGraphSourceRestriction
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPolyhedronFormula

/-! Actual base-triangulation graphs restrict to each entire geometric face carrier. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_base_face_graph {n m : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (A : Set (EuclideanSpace ℝ (Fin m))) (h : K.space → A)
    (G : s2v_t11b_Formula (n + m))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : K.space,
      (∀ i, z (Fin.castAdd m i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = (h x).val i))
    (s : Finset (EuclideanSpace ℝ (Fin n))) (hs : s ∈ K.faces) :
    ∃ F : s2v_t11b_Formula (n + m), ∀ z, z ∈ F.realize ↔
      ∃ x : convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))),
        (∀ i, z (Fin.castAdd m i) = x.val i) ∧
        (∀ i, z (Fin.natAdd n i) = (h ⟨x.val, K.convexHull_subset_space hs x.property⟩).val i) := by
  obtain ⟨C, hC⟩ := s2v_hardt6rb_finite_convexHull_formula (↑s : Set (EuclideanSpace ℝ (Fin n))) s.finite_toSet
  have hsub : C.realize ⊆ K.space := by
    rw [hC]
    exact K.convexHull_subset_space hs
  obtain ⟨F, hF⟩ := s2v_hardt6rb_graph_source_restriction K.space A h G hG C hsub
  refine ⟨F, ?_⟩
  intro z
  rw [hF]
  constructor
  · rintro ⟨x, hx, hy⟩
    exact ⟨⟨x.val, hC ▸ x.property⟩, hx, hy⟩
  · rintro ⟨x, hx, hy⟩
    exact ⟨⟨x.val, hC.symm ▸ x.property⟩, hx, hy⟩

end HodgeLean.Foundations.Program
