import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFacePrisms
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSharedFace
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGeometricRestriction
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBoundaryIntersection

/-! Geometric compatibility of staircase lifts over distinct base simplices. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_global_prism_intersection {E : Type*}
    [AddCommGroup E] [Module ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) (l u : E → ℝ)
    (C : K.faces → Geometry.SimplicialComplex ℝ (E × ℝ))
    (hfaces : ∀ s t, t ∈ (C s).faces ↔ ∃ j : s.val,
      (↑t : Set (E × ℝ)) ⊆
        (((fun i : s.val => (i.val, l i.val)) '' {i | j ≤ i}) ∪
          ((fun i : s.val => (i.val, u i.val)) '' {i | i ≤ j})) ∧ t.Nonempty) :
    ∀ s t r q, r ∈ (C s).faces → q ∈ (C t).faces →
      convexHull ℝ (↑r : Set (E × ℝ)) ∩ convexHull ℝ (↑q : Set (E × ℝ)) ⊆
        convexHull ℝ ((↑r : Set (E × ℝ)) ∩ ↑q) := by
  classical
  have hbase (s : K.faces) (r : Finset (E × ℝ)) (hr : r ∈ (C s).faces) :
      convexHull ℝ (↑r : Set (E × ℝ)) ⊆
        Prod.fst ⁻¹' convexHull ℝ (↑s.val : Set E) := by
    apply convexHull_min
    · intro p hp
      obtain ⟨j, hrj, _⟩ := (hfaces s r).mp hr
      rcases hrj hp with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;>
        exact subset_convexHull ℝ _ i.property
    · exact (convex_convexHull ℝ _).linear_preimage (LinearMap.fst ℝ E ℝ)
  intro s t r q hr hq p hp
  let V := s.val ∩ t.val
  have hpV : p.1 ∈ convexHull ℝ (↑V : Set E) := by
    simpa only [V, Finset.coe_inter] using
      K.inter_subset_convexHull s.property t.property ⟨hbase s r hr hp.1, hbase t q hq hp.2⟩
  have hV : V.Nonempty := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨p.1, hpV⟩)
  have hVK : V ∈ K.faces := K.down_closed s.property Finset.inter_subset_left hV
  let w : K.faces := ⟨V, hVK⟩
  obtain ⟨i, hri, _⟩ := (hfaces s r).mp hr
  obtain ⟨j, hqj, _⟩ := (hfaces t q).mp hq
  have hAB : convexHull ℝ (↑s.val : Set E) ∩ convexHull ℝ (↑t.val : Set E) ⊆
      convexHull ℝ (↑V : Set E) := by
    simpa only [V, Finset.coe_inter] using K.inter_subset_convexHull s.property t.property
  have hsC := s2v_hardt6rb_geometric_prism_restriction s.val V (K.indep s.property)
    Finset.inter_subset_left l u i r hri
  have htC := s2v_hardt6rb_geometric_prism_restriction t.val V (K.indep t.property)
    Finset.inter_subset_right l u j q hqj
  apply s2v_hardt6rb_intersection_of_boundary_complex r q
    (convexHull ℝ (↑s.val : Set E)) (convexHull ℝ (↑t.val : Set E))
    (convexHull ℝ (↑V : Set E)) (↑V : Set E) (C w)
    (hbase s r hr) (hbase t q hq) hAB hsC htC ?_ ?_ hp
  · intro a ha hane
    apply s2v_hardt6rb_shared_prism_face s.val V hV l u (C w) (hfaces w) i a hane
    · intro x hx
      have hx' : x ∈ (↑r : Set (E × ℝ)) ∩ Prod.fst ⁻¹' (↑V : Set E) := ha ▸ hx
      exact hri hx'.1
    · intro x hx
      have hx' : x ∈ (↑r : Set (E × ℝ)) ∩ Prod.fst ⁻¹' (↑V : Set E) := ha ▸ hx
      exact hx'.2
  · intro a ha hane
    apply s2v_hardt6rb_shared_prism_face t.val V hV l u (C w) (hfaces w) j a hane
    · intro x hx
      have hx' : x ∈ (↑q : Set (E × ℝ)) ∩ Prod.fst ⁻¹' (↑V : Set E) := ha ▸ hx
      exact hqj hx'.1
    · intro x hx
      have hx' : x ∈ (↑q : Set (E × ℝ)) ∩ Prod.fst ⁻¹' (↑V : Set E) := ha ▸ hx
      exact hx'.2

end HodgeLean.Foundations.Program
