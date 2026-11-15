import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceContainment
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceCover

/-! Subcomplex membership is constant on every actual intrinsic open face. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_open_face_mem_subcomplex_iff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K D : Geometry.SimplicialComplex ℝ E) (hDK : D.faces ⊆ K.faces)
    (S : Finset E) (hS : S ∈ K.faces) {x : E}
    (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (↑S : Set E))) :
    x ∈ D.space ↔ S ∈ D.faces := by
  constructor
  · intro hxD
    obtain ⟨T, hT, hxT⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hxD
    have hST := s2v_hardt6rb_open_face_subset_of_mem_face K S T hS (hDK hT) hx hxT
    exact D.down_closed hT hST (K.nonempty_of_mem_faces hS)
  · intro hSD
    exact D.convexHull_subset_space hSD (intrinsicInterior_subset hx)

end HodgeLean.Foundations.Program
