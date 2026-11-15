import HodgeLean.Foundations.TubularEuler.MetricNormalLiftHelpers

/-! # Analytic dependence of metric-weighted normal lifting

Both inverse operators vary analytically on the positive metric and surjective transverse locus.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.TubularEuler

variable {B E N : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]
variable [NormedAddCommGroup N] [InnerProductSpace ℝ N] [CompleteSpace N]
variable [FiniteDimensional ℝ N]

theorem metricNormalLift_contDiffOn
    (G : B → E →L[ℝ] E) (D : B → E →L[ℝ] N) (S : Set B)
    (hG : ContDiffOn ℝ ⊤ G S) (hD : ContDiffOn ℝ ⊤ D S)
    (hpos : ∀ p ∈ S, ∀ u : E, u ≠ 0 → 0 < inner ℝ (G p u) u)
    (hsurj : ∀ p ∈ S, Function.Surjective (D p)) :
    ContDiffOn ℝ ⊤ (fun p => metricNormalLift (G p) (D p)) S := by
  have hInvG : ContDiffOn ℝ ⊤ (fun p => ContinuousLinearMap.inverse (G p)) S := by
    intro p hp
    obtain ⟨e, he⟩ := metricOperator_isInvertible_of_positive (G p) (hpos p hp)
    have hi : ContDiffAt ℝ ⊤ ContinuousLinearMap.inverse (G p) := by
      rw [← he]
      exact contDiffAt_map_inverse e
    exact hi.comp_contDiffWithinAt p (hG p hp)
  have hAdj : ContDiffOn ℝ ⊤ (fun p => (D p).adjoint) S :=
    normalAdjoint_contDiff.comp_contDiffOn hD
  have hGram : ContDiffOn ℝ ⊤ (fun p => metricNormalGram (G p) (D p)) S :=
    hD.clm_comp (hInvG.clm_comp hAdj)
  have hInvGram : ContDiffOn ℝ ⊤
      (fun p => ContinuousLinearMap.inverse (metricNormalGram (G p) (D p))) S := by
    intro p hp
    let e := ContinuousLinearEquiv.ofBijective (metricNormalGram (G p) (D p))
      (LinearMap.ker_eq_bot.mpr (metricNormalGram_bijective (G p) (hpos p hp) (D p) (hsurj p hp)).1)
      (LinearMap.range_eq_top.mpr (metricNormalGram_bijective (G p) (hpos p hp) (D p) (hsurj p hp)).2)
    have hi : ContDiffAt ℝ ⊤ ContinuousLinearMap.inverse (metricNormalGram (G p) (D p)) :=
      contDiffAt_map_inverse e
    exact hi.comp_contDiffWithinAt p (hGram p hp)
  exact hInvG.clm_comp (hAdj.clm_comp hInvGram)

#print axioms metricNormalLift_contDiffOn

end HodgeLean.Foundations.TubularEuler
