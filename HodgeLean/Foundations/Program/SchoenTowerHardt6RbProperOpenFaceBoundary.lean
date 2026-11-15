import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceCover
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceContainment

/-! The actual intrinsic boundary of a simplex is the union of its proper intrinsic open faces. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_proper_open_face_boundary {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Geometry.SimplicialComplex ℝ E) (s : L.faces) {x : E}
    (hx : x ∈ convexHull ℝ (s.val : Set E)) :
    x ∉ intrinsicInterior ℝ (convexHull ℝ (s.val : Set E)) ↔
      ∃ t : L.faces, t.val ⊂ s.val ∧ x ∈ intrinsicInterior ℝ (convexHull ℝ (t.val : Set E)) := by
  constructor
  · intro hn
    obtain ⟨T, hT, hxT⟩ := s2v_hardt6rb_mem_open_face L (L.convexHull_subset_space s.property hx)
    have hts := s2v_hardt6rb_open_face_subset_of_mem_face L T s.val hT s.property hxT hx
    refine ⟨⟨T, hT⟩, Finset.ssubset_iff_subset_ne.mpr ⟨hts, ?_⟩, hxT⟩
    intro he
    exact hn (he ▸ hxT)
  · rintro ⟨t, hts, hxt⟩ hxs
    have hst := s2v_hardt6rb_open_face_subset_of_mem_face L s.val t.val s.property t.property hxs
      (intrinsicInterior_subset hxt)
    exact (Finset.ssubset_iff_subset_ne.mp hts).2 (Finset.Subset.antisymm hts.subset hst)

end HodgeLean.Foundations.Program
