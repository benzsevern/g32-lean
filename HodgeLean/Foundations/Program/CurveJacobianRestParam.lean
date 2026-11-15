import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.ProperSpace

/-! # Track B3, lane Rest: smooth parametric integrals

`b3Rest_contDiff_intervalIntegral`: if `F : E × ℝ → G` is smooth, so is `u ↦ ∫ t in a..b, F u t`
(differentiation under the integral sign, by induction on the order, the derivative being the
integral of the partial derivative, which is again smooth).
HC no distance; AV milestone no distance.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ContDiff

namespace HodgeLean.Foundations.Program

universe w

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem b3Rest_contDiff_intervalIntegral_aux (a b : ℝ) (n : ℕ) :
    ∀ (G : Type w) [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] (F : E → ℝ → G),
      ContDiff ℝ ∞ (Function.uncurry F) → ContDiff ℝ n (fun u ↦ ∫ t in a..b, F u t) := by
  induction n with
  | zero =>
    intro G _ _ _ F hF
    exact contDiff_zero.2
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF.continuous a b)
  | succ n ih =>
    intro G _ _ _ F hF
    set F' : E → ℝ → (E →L[ℝ] G) := fun u t ↦
      (fderiv ℝ (Function.uncurry F) (u, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hdiff : Differentiable ℝ (Function.uncurry F) := hF.differentiable (by simp)
    have hpart : ∀ u t, HasFDerivAt (fun x ↦ F x t) (F' u t) u := by
      intro u t
      have h1 : HasFDerivAt (fun x : E ↦ (x, t)) (ContinuousLinearMap.inl ℝ E ℝ) u :=
        (hasFDerivAt_id u).prodMk (hasFDerivAt_const t u)
      exact (hdiff (u, t)).hasFDerivAt.comp u h1
    have hF' : ContDiff ℝ ∞ (Function.uncurry F') := by
      have h1 : ContDiff ℝ ∞ (fderiv ℝ (Function.uncurry F)) := hF.fderiv_right le_rfl
      exact h1.clm_comp contDiff_const
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by norm_cast,
      contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun u ↦ ∫ t in a..b, F' u t, ih (E →L[ℝ] G) F' hF', fun u₀ ↦ ?_⟩
    obtain ⟨M, hM⟩ := (isCompact_closedBall u₀ 1).prod (isCompact_uIcc (a := a) (b := b))
      |>.exists_bound_of_continuousOn hF'.continuous.continuousOn
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ ↦ M)
      (ball_mem_nhds u₀ one_pos) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
    · exact Eventually.of_forall fun u ↦
        (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    · exact (hF'.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · refine Eventually.of_forall fun t ht u hu ↦ hM (u, t) ⟨ball_subset_closedBall hu, ?_⟩
      exact uIoc_subset_uIcc ht
    · exact Eventually.of_forall fun t _ u _ ↦ hpart u t

/-- **Parametric integrals of smooth functions are smooth.** -/
theorem b3Rest_contDiff_intervalIntegral {G : Type w} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {F : E → ℝ → G} (hF : ContDiff ℝ ∞ (Function.uncurry F)) (a b : ℝ) :
    ContDiff ℝ ∞ (fun u ↦ ∫ t in a..b, F u t) :=
  contDiff_infty.2 fun n ↦ b3Rest_contDiff_intervalIntegral_aux a b n G F hF

theorem b3Rest_contDiff_intervalIntegral_comp_aux {P : Type} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] {g : ℝ → P} (hg : Continuous g) (a b : ℝ) (n : ℕ) :
    ∀ (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] (F : E' × P → G),
      ContDiff ℝ ∞ F → ContDiff ℝ n (fun u ↦ ∫ t in a..b, F (u, g t)) := by
  induction n with
  | zero =>
    intro G _ _ _ F hF
    exact contDiff_zero.2 (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun u t ↦ F (u, g t)) (hF.continuous.comp (continuous_fst.prodMk
        (hg.comp continuous_snd))) a b)
  | succ n ih =>
    intro G _ _ _ F hF
    set F' : E' × P → (E' →L[ℝ] G) := fun q ↦ (fderiv ℝ F q).comp (ContinuousLinearMap.inl ℝ E' P)
    have hdiff : Differentiable ℝ F := hF.differentiable (by simp)
    have hpart : ∀ u t, HasFDerivAt (fun x ↦ F (x, g t)) (F' (u, g t)) u := by
      intro u t
      have h1 : HasFDerivAt (fun x : E' ↦ (x, g t)) (ContinuousLinearMap.inl ℝ E' P) u :=
        (hasFDerivAt_id u).prodMk (hasFDerivAt_const (g t) u)
      exact (hdiff (u, g t)).hasFDerivAt.comp u h1
    have hF' : ContDiff ℝ ∞ F' := (hF.fderiv_right le_rfl).clm_comp contDiff_const
    have hc : ∀ (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] (K : E' × P → H),
        Continuous K → Continuous (fun q : E' × ℝ ↦ K (q.1, g q.2)) := fun H _ _ K hK ↦
      hK.comp (continuous_fst.prodMk (hg.comp continuous_snd))
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by norm_cast,
      contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun u ↦ ∫ t in a..b, F' (u, g t), ih (E' →L[ℝ] G) F' hF', fun u₀ ↦ ?_⟩
    obtain ⟨M, hM⟩ := (isCompact_closedBall u₀ 1).prod (isCompact_uIcc (a := a) (b := b))
      |>.exists_bound_of_continuousOn (hc _ F' hF'.continuous).continuousOn
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume)
      (F := fun u t ↦ F (u, g t)) (F' := fun u t ↦ F' (u, g t)) (bound := fun _ ↦ M)
      (ball_mem_nhds u₀ one_pos) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
    · exact Eventually.of_forall fun u ↦
        ((hc _ F hF.continuous).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · exact ((hc _ F hF.continuous).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    · exact ((hc _ F' hF'.continuous).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · refine Eventually.of_forall fun t ht u hu ↦ hM (u, t) ⟨ball_subset_closedBall hu, ?_⟩
      exact uIoc_subset_uIcc ht
    · exact Eventually.of_forall fun t _ u _ ↦ hpart u t

/-- **Parametric integrals along a continuous path**: if `F : E × P → G` is smooth and `g` is
continuous, `u ↦ ∫ t in a..b, F (u, g t)` is smooth. -/
theorem b3Rest_contDiff_intervalIntegral_comp {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] {F : E' × P → G}
    (hF : ContDiff ℝ ∞ F) {g : ℝ → P} (hg : Continuous g) (a b : ℝ) :
    ContDiff ℝ ∞ (fun u ↦ ∫ t in a..b, F (u, g t)) :=
  contDiff_infty.2 fun n ↦ b3Rest_contDiff_intervalIntegral_comp_aux hg a b n G F hF

end HodgeLean.Foundations.Program
