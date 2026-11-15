import HodgeLean.Foundations.Program.G32Native.CanonicalCoefficientForms
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.AbelLocalPrimitives

/-! # Primitive data for the fixed original curve-form basis -/
noncomputable section
set_option maxHeartbeats 400000
open Manifold Set
open scoped ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- The fixed basis has local primitives in exactly the retained scalar line coordinate. -/
theorem canonical_curve_primitive_data (G : CanonicalAbelGeometry)
    (q : AlgebraicGeometry.ComplexPoint G.Z) :
    ∃ R : ℝ, 0 < R ∧
      (∀ z : ℂ, ‖z‖ < R → chartAt (Fin 1 → ℂ) q q +
        z • b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) 1 ∈
          (chartAt (Fin 1 → ℂ) q).target) ∧
      ∃ H : Fin (G.k + 1) → ℂ → ℂ, ∀ i, ∀ z ∈ Metric.ball (0 : ℂ) R,
        HasDerivAt (H i)
          (b3A_discCoef (canonicalFormBasis G i).val q
            (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) 1) z) z := by
  let u := b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) 1
  have hu : u ≠ 0 := (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)).map_ne_zero_iff.mpr one_ne_zero
  obtain ⟨R, hR, hchart⟩ := b3A_chart_radius u hu q
  have hprim (i : Fin (G.k + 1)) : ∃ H : ℂ → ℂ, ∀ z ∈ Metric.ball (0 : ℂ) R,
      HasDerivAt H (b3A_discCoef (canonicalFormBasis G i).val q u z) z :=
    DifferentiableOn.isExactOn_ball (fun z hz =>
      (b3A_discCoef_differentiableAt (canonicalFormBasis G i).property q u
        (hchart z (mem_ball_zero_iff.mp hz))).differentiableWithinAt)
  choose H hH using hprim
  exact ⟨R, hR, hchart, H, hH⟩

#print axioms canonical_curve_primitive_data
end HodgeLean.Foundations.Program.G32Native
