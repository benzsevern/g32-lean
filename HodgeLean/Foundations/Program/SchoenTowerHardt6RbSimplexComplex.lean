import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Combination

/-! The finite geometric complex consisting of all faces of one simplex. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_simplex_complex {E : Type*} [AddCommGroup E] [Module ℝ E]
    (S : Finset E) (hS : AffineIndependent ℝ (fun x : S => (x : E))) :
    ∃ K : Geometry.SimplicialComplex ℝ E,
      (∀ s, s ∈ K.faces ↔ s ⊆ S ∧ s.Nonempty) ∧
      K.faces.Finite ∧ K.space = convexHull ℝ (↑S : Set E) := by
  classical
  let K : Geometry.SimplicialComplex ℝ E :=
    { faces := {s | s ⊆ S ∧ s.Nonempty}
      isRelLowerSet_faces := by
        intro s hs
        exact ⟨hs.2, fun t hts ht => ⟨hts.trans hs.1, ht⟩⟩
      indep := by
        intro s hs
        exact hS.mono (Finset.coe_subset.mpr hs.1)
      inter_subset_convexHull := by
        intro s t hs ht
        exact (hS.convexHull_inter hs.1 ht.1).symm.subset }
  refine ⟨K, fun _ => Iff.rfl, ?_, ?_⟩
  · exact S.powerset.finite_toSet.subset (fun s hs => Finset.mem_powerset.mpr hs.1)
  · ext x
    constructor
    · intro hx
      obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
      exact convexHull_mono (Finset.coe_subset.mpr hs.1) hxs
    · intro hx
      have hne : S.Nonempty := by
        exact Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hx⟩)
      exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨S, ⟨Finset.Subset.refl S, hne⟩, hx⟩

end HodgeLean.Foundations.Program
