import HodgeLean.Foundations.Program.SchoenTowerHardt6RbMappedGraphClosure
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenHullTopology
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

/-! The cell equation and continuous endpoint data imply the refinement's exact closure equation. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_refined_cell_closure {n : ℕ}
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hβ : ContinuousOn β L.space)
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)))
    (s : L.faces) (graph : Bool)
    (l u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hl : ContinuousOn l (convexHull ℝ (↑s.val : Set _)))
    (hu : ContinuousOn u (convexHull ℝ (↑s.val : Set _)))
    (hlu : ∀ x ∈ convexHull ℝ (↑s.val : Set _), l x ≤ u x)
    (hgraph : graph = true → ∀ x ∈ convexHull ℝ (↑s.val : Set _), l x = u x)
    (hband : graph = false → ∀ x ∈ intrinsicInterior ℝ
      (convexHull ℝ (↑s.val : Set _)), l x < u x)
    (c : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hcell : c = e '' {z | ∃ x ∈ intrinsicInterior ℝ
      (convexHull ℝ (↑s.val : Set _)), (∀ j, z j.succ = β x j) ∧
      (if graph then z 0 = l x else l x < z 0 ∧ z 0 < u x)}) :
    closure c = e '' {z | ∃ x ∈ convexHull ℝ (↑s.val : Set _),
      (∀ j, z j.succ = β x j) ∧ l x ≤ z 0 ∧ z 0 ≤ u x} := by
  have hcompact := s.val.finite_toSet.isCompact_convexHull ℝ
  have hdense := (s2v_hardt6rb_open_hull_topology s.val).1
  have hbase := hβ.mono (L.convexHull_subset_space s.property)
  rw [hcell]
  cases graph
  · exact s2v_hardt6rb_mapped_band_closure _ _ hcompact hdense β hbase e
      l u hl hu hlu (hband rfl)
  · have heq : {z : EuclideanSpace ℝ (Fin (n + 1)) |
        ∃ x ∈ convexHull ℝ (↑s.val : Set _), (∀ j, z j.succ = β x j) ∧
          l x ≤ z 0 ∧ z 0 ≤ u x} =
        {z | ∃ x ∈ convexHull ℝ (↑s.val : Set _),
          (∀ j, z j.succ = β x j) ∧ z 0 = l x} := by
      ext z
      constructor
      · rintro ⟨x, hx, hz, hlo, hup⟩
        exact ⟨x, hx, hz, le_antisymm ((hgraph rfl x hx) ▸ hup) hlo⟩
      · rintro ⟨x, hx, hz, ht⟩
        exact ⟨x, hx, hz, ht.ge, ht.trans (hgraph rfl x hx) |>.le⟩
    rw [heq]
    exact s2v_hardt6rb_mapped_graph_closure _ _ hcompact hdense β hbase e l hl

end HodgeLean.Foundations.Program
