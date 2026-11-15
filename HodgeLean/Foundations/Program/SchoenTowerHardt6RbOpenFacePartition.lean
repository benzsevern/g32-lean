import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceSubcomplex

/-! Every point of a geometric complex has a unique actual intrinsic open face. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_unique_open_face {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) {x : E} (hx : x ∈ K.space) :
    ∃! S : Finset E, S ∈ K.faces ∧ x ∈ intrinsicInterior ℝ (convexHull ℝ (↑S : Set E)) := by
  obtain ⟨S, hS, hxS⟩ := s2v_hardt6rb_mem_open_face K hx
  refine ⟨S, ⟨hS, hxS⟩, ?_⟩
  rintro T ⟨hT, hxT⟩
  exact Finset.Subset.antisymm
    (s2v_hardt6rb_open_face_subset_of_mem_face K T S hT hS hxT (intrinsicInterior_subset hxS))
    (s2v_hardt6rb_open_face_subset_of_mem_face K S T hS hT hxS (intrinsicInterior_subset hxT))

end HodgeLean.Foundations.Program
