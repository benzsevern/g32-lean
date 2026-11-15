import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSimplexInteriorDense
import Mathlib.Topology.DenseEmbedding

/-! Order on intrinsic simplex interiors persists for continuous boundary extensions. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_simplex_extension_order {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset E) (f g : convexHull ℝ (↑s : Set E) → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (horder : ∀ x : intrinsicInterior ℝ (convexHull ℝ (↑s : Set E)),
      f ⟨x.val, intrinsicInterior_subset x.property⟩ ≤
        g ⟨x.val, intrinsicInterior_subset x.property⟩) :
    ∀ x, f x ≤ g x := by
  intro x
  exact (s2v_hardt6rb_simplex_interior_dense s).induction_on x (isClosed_le hf hg) horder

end HodgeLean.Foundations.Program
