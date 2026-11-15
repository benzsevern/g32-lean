import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.AffineModel
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open
import Mathlib.AlgebraicGeometry.Noetherian

/-! Finite generators and evaluation on affine open subsets. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.ComplexTopology.Marked

lemma evaluate_appLE {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y)
    (U : Y.left.Opens) (V : X.left.Opens) (e : V ≤ f.left ⁻¹ᵁ U)
    (s : Γ(Y.left, U)) (z : ComplexPoint X) (hz : z ∈ Point.overOpen V) :
    Point.evaluate U s (Point.map f z) =
      Point.evaluate V (f.left.appLE U V e s) z := by
  rw [Point.evaluate_map, Point.evaluate_res e _ z hz]
  rfl

lemma image_iff_generators {X Z : Over (Spec ↧ℂ)} (i : Z ⟶ X)
    [IsClosedImmersion i.left] (U : X.left.affineOpens)
    {m : ℕ} (g : Fin m → Γ(X.left, U.1))
    (hg : Ideal.span (Set.range g) = i.left.ker.ideal U)
    (z : ComplexPoint X) (hz : z.underlying ∈ U.1) :
    z ∈ Set.range (Point.map i) ↔ ∀ k, Point.evaluate U.1 (g k) z = 0 := by
  rw [range_map_of_closedImmersion]
  change z.underlying ∈ Set.range i.left ↔ _
  rw [← i.left.isClosedEmbedding.isClosed_range.closure_eq, ← Scheme.Hom.support_ker]
  change z.underlying ∈ i.left.ker.support ↔ _
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (I := i.left.ker) (U := U) hz, ← hg, Scheme.zeroLocus_span,
    Scheme.mem_zeroLocus_iff]
  simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  apply forall_congr'
  intro k
  exact (not_congr (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero (g k) z hz)).trans
    (not_not)

end HodgeLean.Foundations.ComplexTopology.Marked
