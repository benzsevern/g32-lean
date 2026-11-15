import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBoundaryRayUnique
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbConeCoordinates

/-! Cones over common boundary faces intersect in the cone over the actual common face. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_cone_intersection {E : Type*} [DecidableEq E]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hC : Convex ℝ C) (a : E) (ha : a ∈ intrinsicInterior ℝ C)
    (s t : Finset E) (hs : s.Nonempty) (ht : t.Nonempty)
    (hbs : convexHull ℝ (↑s : Set E) ⊆ C \ intrinsicInterior ℝ C)
    (hbt : convexHull ℝ (↑t : Set E) ⊆ C \ intrinsicInterior ℝ C)
    (hst : convexHull ℝ (↑s : Set E) ∩ convexHull ℝ (↑t : Set E) ⊆
      convexHull ℝ ((↑s : Set E) ∩ ↑t)) :
    convexHull ℝ (↑(insert a s) : Set E) ∩ convexHull ℝ (↑(insert a t) : Set E) ⊆
      convexHull ℝ (insert a ((↑s : Set E) ∩ ↑t)) := by
  intro x hx
  by_cases hxa : x = a
  · subst x
    exact subset_convexHull ℝ _ (Set.mem_insert _ _)
  obtain ⟨y, hy, u, hu, huy⟩ := (s2v_hardt6rb_cone_coordinates a s hs x).mp hx.1
  obtain ⟨z, hz, v, hv, hvz⟩ := (s2v_hardt6rb_cone_coordinates a t ht x).mp hx.2
  have hup : 0 < u := by
    by_contra hn
    have hu0 : u = 0 := le_antisymm (le_of_not_gt hn) hu.1
    exact hxa (by simpa only [hu0, AffineMap.lineMap_apply_zero] using huy.symm)
  have hvp : 0 < v := by
    by_contra hn
    have hv0 : v = 0 := le_antisymm (le_of_not_gt hn) hv.1
    exact hxa (by simpa only [hv0, AffineMap.lineMap_apply_zero] using hvz.symm)
  have hyz := (s2v_hardt6rb_boundary_ray_unique C hC a ha (hbs hy) (hbt hz)
    hup hvp (huy.trans hvz.symm)).2
  subst z
  have hcommon := hst ⟨hy, hz⟩
  have hay : segment ℝ a y ⊆ convexHull ℝ (insert a ((↑s : Set E) ∩ ↑t)) :=
    (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ (Set.mem_insert _ _))
      (convexHull_mono (Set.subset_insert a _) hcommon)
  apply hay
  rw [← huy]
  exact lineMap_mem_segment ℝ a y hu

end HodgeLean.Foundations.Program
