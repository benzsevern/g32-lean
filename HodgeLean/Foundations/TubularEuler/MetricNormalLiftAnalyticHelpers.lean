import HodgeLean.Foundations.TubularEuler.MetricNormalLiftRegularityHelpers

/-! # Analytic metric normal lifting at a transverse point

HC no distance; AV milestone no distance. -/

noncomputable section
namespace HodgeLean.Foundations.TubularEuler

variable {B E N : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]
variable [NormedAddCommGroup N] [InnerProductSpace ℝ N] [CompleteSpace N]
variable [FiniteDimensional ℝ N]

theorem metricNormalLift_analyticAt
    (G : B → E →L[ℝ] E) (D : B → E →L[ℝ] N) (p : B)
    (hG : AnalyticAt ℝ G p) (hD : AnalyticAt ℝ D p)
    (hpos : ∀ u : E, u ≠ 0 → 0 < inner ℝ (G p u) u)
    (hsurj : Function.Surjective (D p)) :
    AnalyticAt ℝ (fun q => metricNormalLift (G q) (D q)) p := by
  have hInvG : AnalyticAt ℝ (fun q => ContinuousLinearMap.inverse (G q)) p := by
    obtain ⟨e, he⟩ := metricOperator_isInvertible_of_positive (G p) hpos
    have hi : AnalyticAt ℝ ContinuousLinearMap.inverse (G p) := by
      rw [← he]
      exact (contDiffAt_map_inverse e).analyticAt
    exact hi.comp hG
  have hAdj : AnalyticAt ℝ (fun q => (D q).adjoint) p :=
    normalAdjoint_contDiff.contDiffAt.analyticAt.comp hD
  have hGram : AnalyticAt ℝ (fun q => metricNormalGram (G q) (D q)) p :=
    (hD.contDiffAt.clm_comp (hInvG.contDiffAt.clm_comp hAdj.contDiffAt)).analyticAt
  let e := ContinuousLinearEquiv.ofBijective (metricNormalGram (G p) (D p))
    (LinearMap.ker_eq_bot.mpr (metricNormalGram_bijective (G p) hpos (D p) hsurj).1)
    (LinearMap.range_eq_top.mpr (metricNormalGram_bijective (G p) hpos (D p) hsurj).2)
  have hi : AnalyticAt ℝ ContinuousLinearMap.inverse (metricNormalGram (G p) (D p)) :=
    (contDiffAt_map_inverse e).analyticAt
  have hInvGram : AnalyticAt ℝ
      (fun q => ContinuousLinearMap.inverse (metricNormalGram (G q) (D q))) p := hi.comp (f := fun q : B => metricNormalGram (G q) (D q)) (x := p) hGram
  exact (hInvG.contDiffAt.clm_comp
    (hAdj.contDiffAt.clm_comp hInvGram.contDiffAt)).analyticAt

#print axioms metricNormalLift_analyticAt

end HodgeLean.Foundations.TubularEuler
