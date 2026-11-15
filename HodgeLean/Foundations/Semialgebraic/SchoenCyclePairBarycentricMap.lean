import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairCoordinateSum

/-! Continuous finite barycentric maps for geometric complexes.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations.Program
namespace Semialgebraic.CompatibleTriangulation.Helpers

/-- A finite vertex set carries a continuous barycentric map reconstructing every carrier point. -/
theorem s2e_pair_barycentric_map {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V) :
    ∃ W : C(K.space, stdSimplex ℝ V),
      (∀ x : K.space, (∑ a : V, (W x).val a • a.val) = x.val) ∧
      (∀ (s : Finset E) (hs : s ∈ K.faces) (w : stdSimplex ℝ s)
        (x : K.space), (∑ i, w.val i • i.val) = x.val →
        ∀ a : V, (W x).val a = if ha : a.val ∈ s then w.val ⟨a.val, ha⟩ else 0) := by
  classical
  obtain ⟨c, hc, hcoord⟩ := s2e_pair_vertex_coordinates K hK
  have hsV (s : Finset E) (hs : s ∈ K.faces) : s ⊆ V := by
    intro a ha
    exact hV a (K.down_closed hs (Finset.singleton_subset_iff.mpr ha)
      (Finset.singleton_nonempty _))
  have hweights (x : K.space) :
      ∃ (s : Finset E) (hs : s ∈ K.faces) (w : stdSimplex ℝ s),
        (∑ i, w.val i • i.val) = x.val := by
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp x.property
    have hr : Set.range (fun i : s => (i.val : E)) = (↑s : Set E) := by
      ext z
      simp only [Set.mem_range, Subtype.exists, exists_prop, exists_eq_right, Finset.mem_coe]
    obtain ⟨w, hw⟩ := (s2v_hardt6rb_convexHull_range_weights _ x.val).mp (hr.symm ▸ hx)
    exact ⟨s, hs, w, hw⟩
  have hlocal (s : Finset E) (hs : s ∈ K.faces) (w : stdSimplex ℝ s)
      (x : K.space) (hx : (∑ i, w.val i • i.val) = x.val) (a : E) :
      c a x.val = if ha : a ∈ s then w.val ⟨a, ha⟩ else 0 := by
    rw [← hx]
    exact hcoord a s hs w
  let W : C(K.space, stdSimplex ℝ V) :=
    { toFun := fun x => ⟨fun a => c a.val x.val, by
        obtain ⟨s, hs, w, hx⟩ := hweights x
        constructor
        · intro a
          change 0 ≤ c a.val x.val
          rw [hlocal s hs w x hx a.val]
          split_ifs
          · exact w.property.1 _
          · exact le_rfl
        · change (∑ a : V, c a.val x.val) = 1
          rw [Finset.sum_coe_sort V (fun a => c a x.val)]
          exact (s2e_pair_coordinate_sum V s (hsV s hs) w.val (fun a => c a x.val)
            (hlocal s hs w x hx) (fun _ t => t) (fun _ => rfl)).trans w.property.2⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_pi (fun a => hc a.val) }
  refine ⟨W, ?_, ?_⟩
  · intro x
    obtain ⟨s, hs, w, hx⟩ := hweights x
    change (∑ a : V, c a.val x.val • a.val) = x.val
    rw [Finset.sum_coe_sort V (fun a => c a x.val • a)]
    exact (s2e_pair_coordinate_sum V s (hsV s hs) w.val (fun a => c a x.val)
      (hlocal s hs w x hx) (fun a t => t • a) (fun _ => zero_smul ℝ _)).trans hx
  · intro s hs w x hx a
    exact hlocal s hs w x hx a.val

end Semialgebraic.CompatibleTriangulation.Helpers
