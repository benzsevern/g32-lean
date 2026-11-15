import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidIncidence

/-! Original subcomplex membership is detected exactly at each original face centroid. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_centroid_mem_subcomplex_iff {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (K D : Geometry.SimplicialComplex ℝ E) (hDK : D.faces ⊆ K.faces)
    (S : Finset E) (hS : S ∈ K.faces) :
    S.centroid ℝ id ∈ D.space ↔ S ∈ D.faces := by
  constructor
  · intro hx
    obtain ⟨T, hT, hxT⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    have hST := (s2v_hardt6rb_centroid_mem_base_face_iff K S T hS (hDK hT)).mp hxT
    exact D.down_closed hT hST (K.nonempty_of_mem_faces hS)
  · intro hsD
    exact D.convexHull_subset_space hsD (S.centroid_mem_convexHull (D.nonempty_of_mem_faces hsD))

end HodgeLean.Foundations.Program
