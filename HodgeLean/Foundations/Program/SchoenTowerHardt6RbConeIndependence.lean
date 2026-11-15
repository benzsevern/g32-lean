import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBoundaryAffineSpan
import Mathlib.LinearAlgebra.AffineSpace.Independent

/-! Coning an independent boundary face from an interior apex preserves affine independence. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_cone_independence {E : Type*} [DecidableEq E]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C : Set E) (hC : Convex ℝ C) (a : E) (ha : a ∈ intrinsicInterior ℝ C)
    (s : Finset E) (hs : s.Nonempty)
    (hi : AffineIndependent ℝ ((↑) : s → E))
    (hb : convexHull ℝ (↑s : Set E) ⊆ C \ intrinsicInterior ℝ C) :
    AffineIndependent ℝ (fun x : {x : E // x ∈ insert a s} => x.val) := by
  classical
  have hnot : a ∉ affineSpan ℝ (↑s : Set E) := by
    rw [← affineSpan_convexHull]
    exact s2v_hardt6rb_boundary_affineSpan C _ hC (convex_convexHull ℝ _)
      hs.to_set.convexHull hb a ha
  have hi' : AffineIndepOn ℝ id (↑s : Set E) := hi
  have hh := hi'.id_insert hnot
  change AffineIndepOn ℝ id (↑(insert a s) : Set E)
  simpa only [Finset.coe_insert] using hh

end HodgeLean.Foundations.Program
