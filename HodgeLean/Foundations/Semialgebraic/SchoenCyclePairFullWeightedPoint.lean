import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSupportedHull
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

/-! Supported convex combinations in a full geometric subcomplex.
HC no distance; AV milestone no distance. -/
noncomputable section
open HodgeLean.Foundations.Program
namespace Semialgebraic.CompatibleTriangulation.Helpers

/-- Weights on marked vertices of one ambient face give a point of the full subcomplex. -/
theorem s2e_pair_full_subcomplex_weighted_point {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (K D : Geometry.SimplicialComplex ℝ E)
    (hfull : ∀ s ∈ K.faces, (∀ a ∈ s, a ∈ D.vertices) → s ∈ D.faces)
    (s : Finset E) (hs : s ∈ K.faces) (v : ι → E) (w : stdSimplex ℝ ι)
    (hsupport : ∀ i, w.val i ≠ 0 → v i ∈ s ∧ v i ∈ D.vertices) :
    (∑ i, w.val i • v i) ∈ D.space := by
  classical
  let T := s.filter (fun a => a ∈ D.vertices)
  have hp : (∑ i, w.val i • v i) ∈ convexHull ℝ (↑T : Set E) := by
    apply s2v_hardt6rb_supported_convexHull v w (↑T : Set E)
    intro i hi
    exact Finset.mem_filter.mpr (hsupport i hi)
  have hT : T.Nonempty :=
    Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨_, hp⟩)
  have hTK : T ∈ K.faces := K.down_closed hs (Finset.filter_subset _ _) hT
  have hTD : T ∈ D.faces :=
    hfull T hTK (fun a ha => (Finset.mem_filter.mp ha).2)
  exact D.convexHull_subset_space hTD hp

end Semialgebraic.CompatibleTriangulation.Helpers
