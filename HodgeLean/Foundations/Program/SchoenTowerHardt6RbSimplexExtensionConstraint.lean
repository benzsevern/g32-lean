import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSimplexInteriorDense
import Mathlib.Topology.DenseEmbedding

/-! Continuous equations on intrinsic simplex interiors persist at every boundary point. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_simplex_extension_constraint {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset E) (g : convexHull ℝ (↑s : Set E) → ℝ) (hg : Continuous g)
    (P : E × ℝ → ℝ) (hP : ContinuousOn P (convexHull ℝ (↑s : Set E) ×ˢ Set.univ))
    (hzero : ∀ x : intrinsicInterior ℝ (convexHull ℝ (↑s : Set E)),
      P (x.val, g ⟨x.val, intrinsicInterior_subset x.property⟩) = 0) :
    ∀ x, P (x.val, g x) = 0 := by
  have hc : Continuous (fun x : convexHull ℝ (↑s : Set E) => P (x.val, g x)) :=
    hP.comp_continuous (continuous_subtype_val.prodMk hg) (fun x => ⟨x.property, trivial⟩)
  intro x
  exact (s2v_hardt6rb_simplex_interior_dense s).induction_on x
    (isClosed_eq hc continuous_const) hzero

end HodgeLean.Foundations.Program
