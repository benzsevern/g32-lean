import HodgeLean.Foundations.Program.G32Native.AbelCollisionCurveTuple
import HodgeLean.Foundations.Program.G32Native.AbelCollisionBlocks
import HodgeLean.Foundations.Program.SchoenCycleMonicRootSelection

/-! # Exact coefficient evaluation on the original curve root tuples -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MvPolynomial
open HodgeLean.Adapters Filter Manifold
open scoped Topology BigOperators ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- Signed mixed chart coordinates are exactly the lower monic coefficients of the original roots. -/
theorem collision_curve_tuple_coefficients
    (Z B : Over (Spec ↧ℂ)) [IsProjective Z.hom] [SmoothOfRelativeDimension 1 Z.hom]
    {n b : ℕ} (γ : g3_power Z n ⟶ B) (x : ComplexPoint (g3_power Z n))
    (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint Z)
    (hx : ∀ a i, Point.map (g3_proj Z n (ι ⟨a, i⟩)) x = p a)
    (e : ComplexPoint B → Fin n → ℂ)
    (he : ∀ᶠ q in 𝓝 x, ∀ a (j : Fin (m a)),
      e (Point.map γ q) (ι ⟨a, j⟩) = (-1 : ℂ) ^ (m a - j.val) *
        aeval (fun i : Fin (m a) =>
          (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)).symm
            (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a)
              (Point.map (g3_proj Z n (ι ⟨a, i⟩)) q) -
             extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a) (p a)))
          (esymm (Fin (m a)) ℂ (m a - j.val))) :
    ∀ᶠ z in 𝓝 (0 : (Σ a, Fin (m a)) → ℂ), ∀ a (j : Fin (m a)),
      e (Point.map γ (collisionCurveTuple Z m ι p z)) (ι ⟨a, j⟩) =
        collisionBlockCoefficients m z ⟨a, j⟩ := by
  have ht : Tendsto (collisionCurveTuple Z m ι p) (𝓝 0) (𝓝 x) := by
    simpa only [collisionCurveTuple_zero Z m ι p x hx] using
      (collisionCurveTuple_continuousAt Z m ι p).tendsto
  have hn : ∀ᶠ z in 𝓝 (0 : (Σ a, Fin (m a)) → ℂ), ∀ s : Σ a, Fin (m a),
      (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)).symm
        (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p s.1)
          (b3A_disc (p s.1) (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) 1) (z s)) -
         extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p s.1) (p s.1)) = z s := by
    apply eventually_all.mpr
    intro s
    exact (original_disc_normalized_coordinate (E := Fin 1 → ℂ) (C := ComplexPoint Z) (Module.finrank_fin_fun (n := 1) ℂ) (p s.1)).comp_tendsto
      (show Tendsto (fun z : (Σ a, Fin (m a)) → ℂ => z s) (𝓝 0) (𝓝 0) from
        (continuous_apply s).continuousAt.tendsto)
  filter_upwards [ht.eventually he, hn] with z hz hzn
  intro a j
  have hc := hz a j
  have hcoords : (fun i : Fin (m a) =>
      (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)).symm
        (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a)
          (Point.map (g3_proj Z n (ι ⟨a, i⟩)) (collisionCurveTuple Z m ι p z)) -
         extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a) (p a))) = (fun i => z ⟨a, i⟩) := by
    funext i
    rw [collisionCurveTuple_projection]
    exact hzn ⟨a, i⟩
  rw [hcoords] at hc
  exact hc.trans (s2e_rootTuple_signed_coefficient (m a) (fun i => z ⟨a, i⟩) j).symm

#print axioms collision_curve_tuple_coefficients
end HodgeLean.Foundations.Program.G32Native
