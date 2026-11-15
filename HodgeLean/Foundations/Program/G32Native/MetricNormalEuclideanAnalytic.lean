import HodgeLean.Foundations.TubularEuler.MetricNormalLiftAnalyticHelpers
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Analytic Euclidean displacement in metric normal coordinates

The inverse-Gram lift and the derivative of the specified embedding vary
analytically together with the original fibre coordinate.
-/

noncomputable section
namespace HodgeLean.Foundations.TubularEuler

theorem metric_normal_euclidean_displacement_analyticAt
    {B E N F : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup N] [InnerProductSpace ℝ N] [CompleteSpace N]
    [FiniteDimensional ℝ N]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (G : B → E →L[ℝ] E) (D : B → E →L[ℝ] N)
    (σ : B → E) (emb : E → F) (b : B) (w : N)
    (hG : AnalyticAt ℝ G b) (hD : AnalyticAt ℝ D b)
    (hσ : AnalyticAt ℝ σ b) (hemb : AnalyticAt ℝ emb (σ b))
    (hpos : ∀ u : E, u ≠ 0 → 0 < inner ℝ (G b u) u)
    (hsurj : Function.Surjective (D b)) :
    AnalyticAt ℝ (fun p : B × N => fderiv ℝ emb (σ p.1)
      (metricNormalLift (G p.1) (D p.1) p.2)) (b, w) := by
  have hLift := metricNormalLift_analyticAt G D b hG hD hpos hsurj
  have hEmb := hemb.fderiv.comp hσ
  have hM : AnalyticAt ℝ
      (fun c => (fderiv ℝ emb (σ c)).comp (metricNormalLift (G c) (D c))) b :=
    (hEmb.contDiffAt.clm_comp hLift.contDiffAt).analyticAt
  have hMf : AnalyticAt ℝ
      (fun p : B × N => (fderiv ℝ emb (σ p.1)).comp
        (metricNormalLift (G p.1) (D p.1))) (b, w) :=
    hM.comp (f := (Prod.fst : B × N → B)) (x := (b, w)) analyticAt_fst
  exact (hMf.contDiffAt.clm_apply analyticAt_snd.contDiffAt).analyticAt

#print axioms metric_normal_euclidean_displacement_analyticAt
end HodgeLean.Foundations.TubularEuler
