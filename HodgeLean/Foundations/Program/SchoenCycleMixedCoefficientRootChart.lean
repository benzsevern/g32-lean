import HodgeLean.Foundations.Program.SchoenCycleCurvePowerRootChart
import HodgeLean.Foundations.Program.SchoenCycleMixedRootSelection

/-! # Exact mixed coefficient identities on actual root charts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MvPolynomial
open HodgeLean.Adapters Filter Topology Manifold
open scoped ContDiff BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- The prescribed mixed coefficient equations pull back to the exact signed elementary polynomials in the actual root-chart variables.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Lemma 2.4, printed p. 15. -/
theorem s2e_mixed_coefficients_on_root_chart
    (Z B : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (γ : g3_power Z n ⟶ B) (x : ComplexPoint (g3_power Z n))
    (b : ℕ) (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint Z)
    (hx : ∀ a i, Point.map (g3_proj Z n (ι ⟨a, i⟩)) x = p a)
    (E : ComplexPoint B → (Fin n → ℂ))
    (he : ∀ᶠ q in 𝓝 x, ∀ a (j : Fin (m a)),
      E (Point.map γ q) (ι ⟨a, j⟩) = (-1 : ℂ) ^ (m a - j.val) *
        aeval (fun i : Fin (m a) =>
          (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)).symm
            (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a) (Point.map (g3_proj Z n (ι ⟨a, i⟩)) q) -
              extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a) (p a)))
          (esymm (Fin (m a)) ℂ (m a - j.val))) :
    ∀ᶠ z : Fin n → ℂ in 𝓝 0, ∀ a (j : Fin (m a)),
      E (Point.map γ (s2e_curvePowerRootChart Z n x
        (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)) z)) (ι ⟨a, j⟩) =
        (-1 : ℂ) ^ (m a - j.val) * aeval (fun i => z (ι ⟨a, i⟩))
          (esymm (Fin (m a)) ℂ (m a - j.val)) := by
  let L := b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)
  have hq := s2e_curvePowerRootChart_tendsto Z n x L
  filter_upwards [hq.eventually he, s2e_curvePowerRootChart_coordinates Z n x L] with z hz hcz
  intro a j
  rw [hz a j]
  have hargs : (fun i : Fin (m a) => L.symm
      (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a)
        (Point.map (g3_proj Z n (ι ⟨a, i⟩)) (s2e_curvePowerRootChart Z n x L z)) -
        extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a) (p a))) = fun i => z (ι ⟨a, i⟩) := by
    funext i
    have h := (hcz (ι ⟨a, i⟩)).2
    rw [hx a i] at h
    simpa only [s2e_native_curve_extChart_apply] using h
  rw [hargs]

end HodgeLean.Foundations.Program
