import HodgeLean.Foundations.Program.SchoenTransferJ12CurvePullback
import HodgeLean.Foundations.Program.SchoenTransferJ12CurveDimension
import HodgeLean.Foundations.Program.SchoenTransferJ12CurvePoints
import HodgeLean.Adapters.AbelianHomPullback

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- The actual finite surjective morphism of curves has injective rational H1 pullback. -/
theorem s4_selected_finite_curve_pullback
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1) (q : X ⟶ Y) [IsFinite q.left]
    (hq : Function.Surjective (Point.map q)) : Function.Injective (homPullback q 1) := by
  classical
  letI := connectedSpace_complexPoint X
  letI := connectedSpace_complexPoint Y
  letI := s4_selected_curve_points_nontrivial Y hdimY
  have hdimX := s4_selected_finite_curve_source_dimension X Y hdimY q hq
  have hX : Module.finrank ℂ (Fin (TopologicalSpace.dim X.left) → ℂ) = 1 := by
    simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
      smul_eq_mul, mul_one] using hdimX
  have hY : Module.finrank ℂ (Fin (TopologicalSpace.dim Y.left) → ℂ) = 1 := by
    simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
      smul_eq_mul, mul_one] using hdimY
  obtain ⟨y₀, y₁, hne⟩ := exists_pair_ne (ComplexPoint Y)
  obtain ⟨x₀, hx₀⟩ := hq y₀
  obtain ⟨x₁, hx₁⟩ := hq y₁
  have hnc : ∃ x x', Point.map q x ≠ Point.map q x' :=
    ⟨x₀, x₁, by simpa only [hx₀, hx₁] using hne⟩
  have hh := spec_contMDiff_pointMap X Y (TopologicalSpace.dim X.left)
    (TopologicalSpace.dim Y.left) q
  have hs := s4_selected_curve_pullback_injective hX hY (Point.map q) hh hnc
  exact (cupComparison X 1).symm.injective.comp (hs.comp (cupComparison Y 1).injective)

#print axioms s4_selected_finite_curve_pullback

end HodgeLean.Foundations.Program
