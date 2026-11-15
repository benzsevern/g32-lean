import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGeometricCentroidRestriction
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidIncidence

/-! Common-face intersections for centroid chains over distinct faces of a geometric complex. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_global_centroid_chain_intersection {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (C D : Finset (Finset E))
    (hCK : ∀ S ∈ C, S ∈ K.faces) (hDK : ∀ S ∈ D, S ∈ K.faces)
    (hC : ∀ S ∈ C, ∀ T ∈ C, S ⊆ T ∨ T ⊆ S)
    (hD : ∀ S ∈ D, ∀ T ∈ D, S ⊆ T ∨ T ⊆ S) :
    convexHull ℝ ((fun T : Finset E => T.centroid ℝ id) '' (↑C : Set (Finset E))) ∩
        convexHull ℝ ((fun T : Finset E => T.centroid ℝ id) '' (↑D : Set (Finset E))) =
      convexHull ℝ (((fun T : Finset E => T.centroid ℝ id) '' (↑C : Set (Finset E))) ∩
        ((fun T : Finset E => T.centroid ℝ id) '' (↑D : Set (Finset E)))) := by
  classical
  apply Set.Subset.antisymm ?_
    (Set.subset_inter (convexHull_mono Set.inter_subset_left) (convexHull_mono Set.inter_subset_right))
  rintro p ⟨hpC, hpD⟩
  have hCne : C.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simpa only [he, Finset.coe_empty, Set.image_empty, convexHull_empty, Set.notMem_empty] using hpC
  have hDne : D.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simpa only [he, Finset.coe_empty, Set.image_empty, convexHull_empty, Set.notMem_empty] using hpD
  obtain ⟨S, hS, hmaxC⟩ := s2v_hardt6rb_face_chain_max C hCne hC
  obtain ⟨T, hT, hmaxD⟩ := s2v_hardt6rb_face_chain_max D hDne hD
  have hsK := hCK S hS
  have htK := hDK T hT
  have hpS : p ∈ convexHull ℝ (↑S : Set E) := by
    apply (convexHull_min ?_ (convex_convexHull ℝ (↑S : Set E))) hpC
    rintro x ⟨U, hU, rfl⟩
    exact (s2v_hardt6rb_centroid_mem_base_face_iff K U S (hCK U hU) hsK).mpr (hmaxC U hU)
  have hpT : p ∈ convexHull ℝ (↑T : Set E) := by
    apply (convexHull_min ?_ (convex_convexHull ℝ (↑T : Set E))) hpD
    rintro x ⟨U, hU, rfl⟩
    exact (s2v_hardt6rb_centroid_mem_base_face_iff K U T (hDK U hU) htK).mpr (hmaxD U hU)
  let V := S ∩ T
  have hpV : p ∈ convexHull ℝ (↑V : Set E) := by
    simpa only [V, Finset.coe_inter] using K.inter_subset_convexHull hsK htK ⟨hpS, hpT⟩
  have hV : V.Nonempty := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨p, hpV⟩)
  have hVK := K.down_closed hsK Finset.inter_subset_left hV
  have hneC : ∀ U ∈ C, U.Nonempty := fun U hU => K.nonempty_of_mem_faces (hCK U hU)
  have hneD : ∀ U ∈ D, U.Nonempty := fun U hU => K.nonempty_of_mem_faces (hDK U hU)
  let C' := C.filter (fun U => U ⊆ V)
  let D' := D.filter (fun U => U ⊆ V)
  have hresC := s2v_hardt6rb_geometric_centroid_chain_restriction S V (K.indep hsK)
    Finset.inter_subset_left C hmaxC hneC hC
  have hresD := s2v_hardt6rb_geometric_centroid_chain_restriction T V (K.indep htK)
    Finset.inter_subset_right D hmaxD hneD hD
  have hpC' : p ∈ convexHull ℝ ((fun U : Finset E => U.centroid ℝ id) '' (↑C' : Set (Finset E))) := by
    rw [← hresC]
    exact ⟨hpC, hpV⟩
  have hpD' : p ∈ convexHull ℝ ((fun U : Finset E => U.centroid ℝ id) '' (↑D' : Set (Finset E))) := by
    rw [← hresD]
    exact ⟨hpD, hpV⟩
  have hsubC' : ∀ U ∈ C', U ⊆ V := fun U hU => (Finset.mem_filter.mp hU).2
  have hsubD' : ∀ U ∈ D', U ⊆ V := fun U hU => (Finset.mem_filter.mp hU).2
  have hneC' : ∀ U ∈ C', U.Nonempty := fun U hU => hneC U (Finset.mem_filter.mp hU).1
  have hneD' : ∀ U ∈ D', U.Nonempty := fun U hU => hneD U (Finset.mem_filter.mp hU).1
  have hC' : ∀ U ∈ C', ∀ W ∈ C', U ⊆ W ∨ W ⊆ U :=
    fun U hU W hW => hC U (Finset.mem_filter.mp hU).1 W (Finset.mem_filter.mp hW).1
  have hD' : ∀ U ∈ D', ∀ W ∈ D', U ⊆ W ∨ W ⊆ U :=
    fun U hU W hW => hD U (Finset.mem_filter.mp hU).1 W (Finset.mem_filter.mp hW).1
  have hinter := s2v_hardt6rb_geometric_centroid_chain_intersection V (K.indep hVK)
    C' D' hsubC' hsubD' hneC' hneD' hC' hD'
  have hp' : p ∈ convexHull ℝ
      (((fun U : Finset E => U.centroid ℝ id) '' (↑C' : Set (Finset E))) ∩
        ((fun U : Finset E => U.centroid ℝ id) '' (↑D' : Set (Finset E)))) := by
    rw [← hinter]
    exact ⟨hpC', hpD'⟩
  apply convexHull_mono ?_ hp'
  rintro x ⟨⟨U, hU, hUx⟩, ⟨W, hW, hWx⟩⟩
  exact ⟨⟨U, (Finset.mem_filter.mp hU).1, hUx⟩, ⟨W, (Finset.mem_filter.mp hW).1, hWx⟩⟩

end HodgeLean.Foundations.Program
