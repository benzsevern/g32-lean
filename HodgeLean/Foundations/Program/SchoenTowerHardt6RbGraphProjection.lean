import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGlobalPrism
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismProjection
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGraphFiber

/-! Projection is injective on the global geometric lift of prescribed vertex heights. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_graph_projection_injective {E : Type*}
    [AddCommGroup E] [Module ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) (a : E → ℝ)
    (L : Geometry.SimplicialComplex ℝ (E × ℝ))
    (hfaces : ∀ r, r ∈ L.faces ↔ ∃ s ∈ K.faces, ∃ j : s,
      (↑r : Set (E × ℝ)) ⊆
        (((fun i : s => (i.val, a i.val)) '' {i | j ≤ i}) ∪
          ((fun i : s => (i.val, a i.val)) '' {i | i ≤ j})) ∧ r.Nonempty) :
    Function.Injective (fun p : L.space => p.val.1) := by
  classical
  intro p q hpq
  change p.val.1 = q.val.1 at hpq
  obtain ⟨r, hr, hpr⟩ := Geometry.SimplicialComplex.mem_space_iff.mp p.property
  obtain ⟨r', hr', hqr⟩ := Geometry.SimplicialComplex.mem_space_iff.mp q.property
  obtain ⟨s, hs, j, hrj, _⟩ := (hfaces r).mp hr
  obtain ⟨t, ht, j', hrj', _⟩ := (hfaces r').mp hr'
  let V := s ∩ t
  have hpV : p.val.1 ∈ convexHull ℝ (↑V : Set E) := by
    simpa only [V, Finset.coe_inter] using K.inter_subset_convexHull hs ht
      ⟨s2v_hardt6rb_prism_face_projection s a a j r hrj hpr,
        hpq.symm ▸ s2v_hardt6rb_prism_face_projection t a a j' r' hrj' hqr⟩
  have hqV : q.val.1 ∈ convexHull ℝ (↑V : Set E) := hpq ▸ hpV
  have hV : V.Nonempty := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨p.val.1, hpV⟩)
  have hVK : V ∈ K.faces := K.down_closed hs Finset.inter_subset_left hV
  have hrestrict := s2v_hardt6rb_geometric_prism_restriction s V (K.indep hs)
    Finset.inter_subset_left a a j r hrj
  have hrestrict' := s2v_hardt6rb_geometric_prism_restriction t V (K.indep ht)
    Finset.inter_subset_right a a j' r' hrj'
  have hpgraph : p.val ∈ convexHull ℝ (Set.range (fun i : V => (i.val, a i.val))) := by
    have hpp : p.val ∈ convexHull ℝ ((↑r : Set (E × ℝ)) ∩ Prod.fst ⁻¹' (↑V : Set E)) := by
      rw [← hrestrict]
      exact ⟨hpr, hpV⟩
    apply convexHull_mono ?_ hpp
    rintro x ⟨hxr, hxV⟩
    rcases hrj hxr with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;>
      exact ⟨⟨i.val, hxV⟩, rfl⟩
  have hqgraph : q.val ∈ convexHull ℝ (Set.range (fun i : V => (i.val, a i.val))) := by
    have hqq : q.val ∈ convexHull ℝ ((↑r' : Set (E × ℝ)) ∩ Prod.fst ⁻¹' (↑V : Set E)) := by
      rw [← hrestrict']
      exact ⟨hqr, hqV⟩
    apply convexHull_mono ?_ hqq
    rintro x ⟨hxr, hxV⟩
    rcases hrj' hxr with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;>
      exact ⟨⟨i.val, hxV⟩, rfl⟩
  exact Subtype.ext (s2v_hardt6rb_graph_simplex_fiber V (K.indep hVK) a p.val q.val hpgraph hqgraph hpq)

end HodgeLean.Foundations.Program
