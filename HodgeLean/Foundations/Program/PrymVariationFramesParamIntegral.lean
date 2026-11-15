import HodgeLean.Foundations.AnalyticDivisorAlgebraic2
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

noncomputable section
open Set Filter Topology Metric
namespace HodgeLean.Foundations.Program

theorem b63e_analyticAt_intervalIntegral {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] {Φ : W × ℂ → ℂ} {x₀ : W}
    (hΦ : ∀ t ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ Φ (x₀, (t : ℂ))) :
    AnalyticAt ℂ (fun x ↦ ∫ t in (0 : ℝ)..1, Φ (x, (t : ℂ))) x₀ := by
  set c : ℝ → ℝ := fun t ↦ max 0 (min 1 t)
  have hcc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hcI : ∀ t, c t ∈ Icc (0 : ℝ) 1 := fun t ↦
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hc : ∀ t ∈ uIcc (0 : ℝ) 1, c t = t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    simp only [c, min_eq_right ht.2, max_eq_right ht.1]
  have hrw : ∀ x, ∫ t in (0 : ℝ)..1, Φ (x, (t : ℂ)) = ∫ t in (0 : ℝ)..1, Φ (x, (c t : ℂ)) :=
    fun x ↦ intervalIntegral.integral_congr fun t ht ↦ by rw [hc t ht]
  simp_rw [hrw]
  set S : Set ℂ := (fun t : ℝ ↦ (t : ℂ)) '' Icc 0 1
  have hS : IsCompact S := isCompact_Icc.image Complex.continuous_ofReal
  have hcS : ∀ t, (c t : ℂ) ∈ S := fun t ↦ ⟨c t, hcI t, rfl⟩
  set O : Set (W × ℂ) := {p | AnalyticAt ℂ Φ p}
  have hO : IsOpen O := isOpen_analyticAt ℂ Φ
  have hKO : ({x₀} ×ˢ S : Set (W × ℂ)) ⊆ O := by
    rintro ⟨x, w⟩ ⟨hx, t, ht, rfl⟩
    rw [mem_singleton_iff] at hx; subst hx
    exact hΦ t ht
  obtain ⟨η, hη, hηO⟩ :=
    (isCompact_singleton.prod hS).exists_cthickening_subset_open hO hKO
  set K : Set (W × ℂ) := closedBall x₀ η ×ˢ S
  have hKc : IsCompact K := (isCompact_closedBall x₀ η).prod hS
  have hK : K ⊆ O := by
    rintro ⟨x, w⟩ ⟨hx, hw⟩
    refine hηO (mem_cthickening_of_dist_le (x, w) (x₀, w) η _ ⟨rfl, hw⟩ ?_)
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
    exact hx
  have hFc : ContinuousOn Φ K := fun p hp ↦ (hK hp).continuousAt.continuousWithinAt
  have hF'c : ContinuousOn (fderiv ℂ Φ) K :=
    fun p hp ↦ (hK hp).fderiv.continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hF'c
  set ε := η / 2
  have hε : 0 < ε := half_pos hη
  have hsub : ∀ x₁ ∈ ball x₀ ε, ∀ x ∈ ball x₁ ε, x ∈ closedBall x₀ η := by
    intro x₁ hx₁ x hx
    rw [mem_ball] at hx₁ hx; rw [mem_closedBall]
    have : ε = η / 2 := rfl
    linarith [dist_triangle x x₁ x₀]
  have hmemK : ∀ x ∈ closedBall x₀ η, ∀ t : ℝ, (x, (c t : ℂ)) ∈ K :=
    fun x hx t ↦ ⟨hx, hcS t⟩
  have hcont : ∀ x ∈ closedBall x₀ η, Continuous fun t : ℝ ↦ Φ (x, (c t : ℂ)) := fun x hx ↦
    hFc.comp_continuous (continuous_const.prodMk (Complex.continuous_ofReal.comp hcc))
      (hmemK x hx)
  have hdiff : DifferentiableOn ℂ (fun x ↦ ∫ t in (0 : ℝ)..1, Φ (x, (c t : ℂ))) (ball x₀ ε) := by
    intro x₁ hx₁
    refine HasFDerivAt.differentiableAt (f' := ∫ t in (0 : ℝ)..1,
      (fderiv ℂ Φ (x₁, (c t : ℂ))).comp (ContinuousLinearMap.inl ℂ W ℂ)) ?_
      |>.differentiableWithinAt
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
      (μ := MeasureTheory.volume)
      (F := fun x t ↦ Φ (x, (c t : ℂ)))
      (F' := fun x t ↦ (fderiv ℂ Φ (x, (c t : ℂ))).comp (ContinuousLinearMap.inl ℂ W ℂ))
      (bound := fun _ ↦ C * ‖ContinuousLinearMap.inl ℂ W ℂ‖) (ball_mem_nhds x₁ hε)
      ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [ball_mem_nhds x₁ hε] with x hx
      exact (hcont x (hsub x₁ hx₁ x hx)).aestronglyMeasurable
    · exact (hcont x₁ (hsub x₁ hx₁ x₁ (mem_ball_self hε))).intervalIntegrable _ _
    · have hx₁K := hsub x₁ hx₁ x₁ (mem_ball_self hε)
      refine Continuous.aestronglyMeasurable ?_
      exact (ContinuousLinearMap.compL ℂ W (W × ℂ) ℂ).flip (ContinuousLinearMap.inl ℂ W ℂ)
        |>.continuous.comp (hF'c.comp_continuous
          (continuous_const.prodMk (Complex.continuous_ofReal.comp hcc)) (hmemK x₁ hx₁K))
    · refine Eventually.of_forall fun t _ x hx ↦ ?_
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      exact mul_le_mul_of_nonneg_right (hC _ (hmemK x (hsub x₁ hx₁ x hx) t)) (norm_nonneg _)
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun t _ x hx ↦ ?_
      have hd := (hK (hmemK x (hsub x₁ hx₁ x hx) t)).differentiableAt.hasFDerivAt
      exact hd.comp x (hasFDerivAt_prodMk_left (𝕜 := ℂ) x (c t : ℂ))
  exact AnalyticDivisorAlgebraic2.spec_analyticOnNhd_of_differentiableOn isOpen_ball hdiff x₀
    (mem_ball_self hε)

end HodgeLean.Foundations.Program
