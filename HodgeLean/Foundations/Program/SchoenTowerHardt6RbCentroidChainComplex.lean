import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidChain
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSimplexComplex

/-! The actual geometric simplex complex carried by a chain of face centroids. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_centroid_chain_complex {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] (v : ι → E) (hv : AffineIndependent ℝ v)
    (C : Finset (Finset ι)) (hne : ∀ T ∈ C, T.Nonempty)
    (hchain : ∀ S ∈ C, ∀ T ∈ C, S ⊆ T ∨ T ⊆ S) :
    ∃ K : Geometry.SimplicialComplex ℝ E,
      (∀ s, s ∈ K.faces ↔
        (↑s : Set E) ⊆ (fun T => T.centroid ℝ v) '' (↑C : Set (Finset ι)) ∧ s.Nonempty) ∧
      K.faces.Finite ∧
      K.space = convexHull ℝ ((fun T => T.centroid ℝ v) '' (↑C : Set (Finset ι))) := by
  classical
  let S := C.image (fun T => T.centroid ℝ v)
  have hi := (s2v_hardt6rb_centroid_chain_independent v hv C hne hchain).range
  change AffineIndependent ℝ (fun x : Set.range (fun T : C => T.val.centroid ℝ v) => x.val) at hi
  have hrange : Set.range (fun T : C => T.val.centroid ℝ v) = (↑S : Set E) := by
    ext x
    simp only [Set.mem_range, Function.comp_apply, Subtype.exists, exists_prop,
      S, Finset.mem_coe, Finset.mem_image]
  have hS : AffineIndependent ℝ (fun x : S => (x.val : E)) := by
    rw [hrange] at hi
    exact hi
  obtain ⟨K, hfaces, hfinite, hspace⟩ := s2v_hardt6rb_simplex_complex S hS
  have hset : (↑S : Set E) = (fun T => T.centroid ℝ v) '' (↑C : Set (Finset ι)) :=
    Finset.coe_image
  refine ⟨K, ?_, hfinite, ?_⟩
  · intro s
    rw [hfaces, ← hset]
    exact and_congr (Finset.coe_subset.symm) Iff.rfl
  · exact hspace.trans (congrArg (convexHull ℝ) hset)

end HodgeLean.Foundations.Program
