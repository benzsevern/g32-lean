import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGeometricCentroidChain
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

/-! Every face chain in a geometric complex has independent actual centroid vertices. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_global_centroid_chain_independent {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (C : Finset (Finset E))
    (hCK : ∀ S ∈ C, S ∈ K.faces)
    (hchain : ∀ S ∈ C, ∀ T ∈ C, S ⊆ T ∨ T ⊆ S) :
    AffineIndepOn ℝ (fun T : Finset E => T.centroid ℝ id) (↑C : Set (Finset E)) := by
  classical
  by_cases hC : C.Nonempty
  · obtain ⟨S, hS, hmax⟩ := s2v_hardt6rb_face_chain_max C hC hchain
    exact s2v_hardt6rb_geometric_centroid_chain_independent S (K.indep (hCK S hS)) C hmax
      (fun T hT => K.nonempty_of_mem_faces (hCK T hT)) hchain
  · have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    simp only [he, Finset.coe_empty, affineIndepOn_empty]

end HodgeLean.Foundations.Program
