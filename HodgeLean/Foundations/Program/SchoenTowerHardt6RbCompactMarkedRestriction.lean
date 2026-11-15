import HodgeLean.Foundations.Program.SchoenTowerHardt6RbClosedMarkSubcomplex
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCellBoundaryGraphRestriction
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPolyhedronFormula
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbMarkPreimage
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceSubcomplex

/-! Restrict an actual compatible triangulation to a compact marked carrier while retaining every mark and its graph. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_compact_marked_restriction {n m : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) (hK : K.faces.Finite)
    (A M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsCompact M) (hMA : M ⊆ A)
    (B : Fin m → Set (EuclideanSpace ℝ (Fin n))) (H : K.space ≃ₜ A)
    (S : Finset (Finset (EuclideanSpace ℝ (Fin n)))) (hS : (↑S : Set _) ⊆ K.faces)
    (hSM : A ∩ M = (fun x : K.space => (H x).val) ''
      {x : K.space | ∃ s ∈ S, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))})
    (hmarks : ∀ j, ∃ R : Finset (Finset (EuclideanSpace ℝ (Fin n))),
      (↑R : Set _) ⊆ K.faces ∧ A ∩ B j = (fun x : K.space => (H x).val) ''
        {x : K.space | ∃ s ∈ R, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))})
    (G : s2v_t11b_Formula (n + n))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : K.space,
      (∀ i, z (Fin.castAdd n i) = x.val i) ∧ (∀ i, z (Fin.natAdd n i) = (H x).val i)) :
    ∃ D : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)), D.faces.Finite ∧
      ∃ h : D.space ≃ₜ M,
        (∀ j, ∃ R : Finset (Finset (EuclideanSpace ℝ (Fin n))),
          (↑R : Set _) ⊆ D.faces ∧ M ∩ B j = (fun x : D.space => (h x).val) ''
            {x : D.space | ∃ s ∈ R, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))}) ∧
        ∃ J : s2v_t11b_Formula (n + n), ∀ z, z ∈ J.realize ↔ ∃ x : D.space,
          (∀ i, z (Fin.castAdd n i) = x.val i) ∧ (∀ i, z (Fin.natAdd n i) = (h x).val i) := by
  classical
  obtain ⟨D, hD, hDK, hmem⟩ := s2v_hardt6rb_closed_mark_subcomplex K hK A M H
    (hM.isClosed.preimage continuous_subtype_val) S hS hSM
  have hspace : D.space ⊆ K.space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    exact K.convexHull_subset_space (hDK hs) hxs
  obtain ⟨F, hF⟩ := s2v_hardt6rb_complex_carrier_formula D hD
  obtain ⟨h, J, hh, hJ⟩ := s2v_hardt6rb_cell_boundary_graph_restriction K.space D.space A M hspace hMA H
    (fun x => (hmem x).symm) F hF G hG
  refine ⟨D, hD, h, ?_, J, hJ⟩
  intro j
  obtain ⟨R, hRK, hRB⟩ := hmarks j
  let Q := R.filter (fun s => s ∈ D.faces)
  have hQB (x : D.space) : (h x).val ∈ B j ↔
      ∃ s ∈ Q, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _)) := by
    rw [hh]
    rw [s2v_hardt6rb_mark_selection_preimage K.space A (B j) H _ hRB]
    constructor
    · rintro ⟨s, hs, hxs⟩
      exact ⟨s, Finset.mem_filter.mpr ⟨hs,
        (s2v_hardt6rb_open_face_mem_subcomplex_iff K D hDK s (hRK hs) hxs).mp x.property⟩, hxs⟩
    · rintro ⟨s, hs, hxs⟩
      exact ⟨s, (Finset.mem_filter.mp hs).1, hxs⟩
  refine ⟨Q, fun s hs => (Finset.mem_filter.mp hs).2, ?_⟩
  ext y
  constructor
  · rintro ⟨hyM, hyB⟩
    let x := h.symm ⟨y, hyM⟩
    have he : (h x).val = y := congrArg Subtype.val (h.apply_symm_apply ⟨y, hyM⟩)
    exact ⟨x, (hQB x).mp (he.symm ▸ hyB), he⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(h x).property, (hQB x).mpr hx⟩

end HodgeLean.Foundations.Program
