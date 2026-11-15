import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGraphProjection
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGlobalPrismCarrier
import Mathlib.Topology.Homeomorph.Lemmas

/-! The geometric graph of prescribed vertex heights projects homeomorphically onto the base. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_graph_projection_homeomorph {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ (E))
    (a : E → ℝ)
    (L : Geometry.SimplicialComplex ℝ (E × ℝ))
    (hL : L.faces.Finite)
    (hfaces : ∀ r, r ∈ L.faces ↔ ∃ s ∈ K.faces, ∃ j : s,
      (↑r : Set (E × ℝ)) ⊆
        (((fun i : s => (i.val, a i.val)) '' {i | j ≤ i}) ∪
          ((fun i : s => (i.val, a i.val)) '' {i | i ≤ j})) ∧ r.Nonempty) :
    ∃ e : L.space ≃ₜ K.space, ∀ p, (e p).val = p.val.1 := by
  classical
  have hbase (p : L.space) : p.val.1 ∈ K.space := by
    obtain ⟨r, hr, hpr⟩ := Geometry.SimplicialComplex.mem_space_iff.mp p.property
    obtain ⟨s, hs, j, hrj, _⟩ := (hfaces r).mp hr
    exact K.convexHull_subset_space hs (s2v_hardt6rb_prism_face_projection s a a j r hrj hpr)
  let φ : L.space → K.space := fun p => ⟨p.val.1, hbase p⟩
  have hinj : Function.Injective φ := by
    intro p q hpq
    exact s2v_hardt6rb_graph_projection_injective K a L hfaces (congrArg Subtype.val hpq)
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp x.property
    have hrange : Set.range (fun i : s => (i.val : E)) =
        (↑s : Set (E)) := by
      ext z
      simp only [Set.mem_range, Subtype.exists, exists_prop, exists_eq_right, Finset.mem_coe]
    rw [← hrange] at hxs
    obtain ⟨w, hw⟩ := (s2v_hardt6rb_convexHull_range_weights _ x.val).mp hxs
    have hcarrier := s2v_hardt6rb_global_prism_carrier K a a (fun _ _ => le_rfl) L hfaces
    have hp : (x.val, ∑ i, w.val i * a i.val) ∈ L.space := by
      rw [hcarrier]
      exact ⟨s, hs, w, hw, le_rfl, le_rfl⟩
    exact ⟨⟨(x.val, ∑ i, w.val i * a i.val), hp⟩, Subtype.ext rfl⟩
  have hcompact : IsCompact L.space :=
    hL.isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)
  letI : CompactSpace L.space := isCompact_iff_compactSpace.mp hcompact
  let e := Equiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : Continuous e := (continuous_fst.comp continuous_subtype_val).subtype_mk _
  exact ⟨he.homeoOfEquivCompactToT2, fun _ => rfl⟩

end HodgeLean.Foundations.Program
