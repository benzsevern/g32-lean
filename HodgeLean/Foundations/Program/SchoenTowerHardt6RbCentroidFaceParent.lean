import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGlobalSubdivision
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidIntrinsic
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbIntrinsicContainment
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceContainment
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSimplexInteriorConnected

/-! Centroid subdivision faces have nested actual parent faces and an interior parent vertex. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_centroid_face_parents {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    ∃ L : Geometry.SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      ∃ parent : L.faces → K.faces,
        (∀ s, (parent s).val.centroid ℝ id ∈ s.val) ∧
        (∀ s, convexHull ℝ (s.val : Set E) ⊆ convexHull ℝ ((parent s).val : Set E)) ∧
        (∀ s, intrinsicInterior ℝ (convexHull ℝ (s.val : Set E)) ⊆
          intrinsicInterior ℝ (convexHull ℝ ((parent s).val : Set E))) ∧
        (∀ s t, t.val ⊆ s.val → (parent t).val ⊆ (parent s).val) := by
  classical
  obtain ⟨L, hL, hfaces, hspace⟩ := s2v_hardt6rb_centroid_subdivision K hK
  have hparent (s : L.faces) : ∃ M : K.faces,
      M.val.centroid ℝ id ∈ s.val ∧
      convexHull ℝ (s.val : Set E) ⊆ convexHull ℝ (M.val : Set E) := by
    obtain ⟨C, hCK, hchain, hsub, hne⟩ := (hfaces s.val).mp s.property
    let D := C.filter (fun T => T.centroid ℝ id ∈ s.val)
    have hD : D.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      obtain ⟨T, hT, rfl⟩ := hsub hx
      exact ⟨T, Finset.mem_filter.mpr ⟨hT, hx⟩⟩
    have hDC : D ⊆ C := Finset.filter_subset _ _
    obtain ⟨M, hM, hmax⟩ := s2v_hardt6rb_face_chain_max D hD
      (fun S hS T hT => hchain S (hDC hS) T (hDC hT))
    refine ⟨⟨M, hCK M (hDC hM)⟩, (Finset.mem_filter.mp hM).2, ?_⟩
    apply convexHull_min _ (convex_convexHull ℝ (M : Set E))
    intro x hx
    obtain ⟨T, hT, rfl⟩ := hsub hx
    exact (s2v_hardt6rb_centroid_mem_base_face_iff K T M (hCK T hT) (hCK M (hDC hM))).mpr
      (hmax T (Finset.mem_filter.mpr ⟨hT, hx⟩))
  choose parent hv hh using hparent
  have hi (s : L.faces) : intrinsicInterior ℝ (convexHull ℝ (s.val : Set E)) ⊆
      intrinsicInterior ℝ (convexHull ℝ ((parent s).val : Set E)) := by
    apply s2v_hardt6rb_intrinsicInterior_subset_of_meets (hh s) (convex_convexHull ℝ _)
    exact ⟨_, subset_convexHull ℝ _ (hv s),
      s2v_hardt6rb_centroid_intrinsic (parent s).val (K.nonempty_of_mem_faces (parent s).property)⟩
  refine ⟨L, hL, hspace, parent, hv, hh, hi, ?_⟩
  intro s t hts
  obtain ⟨x, hx⟩ := (s2v_hardt6rb_simplex_interior_connected t.val
    (L.nonempty_of_mem_faces t.property)).nonempty
  exact s2v_hardt6rb_open_face_subset_of_mem_face K _ _ (parent t).property (parent s).property
    (hi t hx) (hh s (convexHull_mono (Finset.coe_subset.mpr hts) (intrinsicInterior_subset hx)))

end HodgeLean.Foundations.Program
