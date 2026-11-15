import HodgeLean.Foundations.Program.HolomorphicODEDefs
import HodgeLean.Foundations.Program.HolomorphicODEAnalytic

noncomputable section
open Set Metric Filter Topology MeasureTheory
open scoped Interval
namespace HodgeLean.Foundations.Program

def b65_retract {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (z : P) (δ : ℝ) (x : P) : P := z + (δ / max δ ‖x - z‖) • (x - z)

theorem b65_retract_continuous {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (z : P) {δ : ℝ} (hδ : 0 < δ) : Continuous (b65_retract z δ) := by
  unfold b65_retract
  apply continuous_const.add
  apply Continuous.smul
  · exact continuous_const.div (continuous_const.max (continuous_id.sub continuous_const).norm)
      (fun x ↦ ne_of_gt (hδ.trans_le (le_max_left _ _)))
  · fun_prop

theorem b65_retract_mem {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (z : P) {δ : ℝ} (hδ : 0 < δ) (x : P) : b65_retract z δ x ∈ closedBall z δ := by
  rw [mem_closedBall, dist_eq_norm, b65_retract, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (div_nonneg hδ.le (hδ.trans_le (le_max_left _ _)).le)]
  rw [div_mul_eq_mul_div, div_le_iff₀ (hδ.trans_le (le_max_left _ _))]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) hδ.le

theorem b65_retract_eq {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (z : P) {δ : ℝ} (hδ : 0 < δ) {x : P} (hx : x ∈ ball z δ) :
    b65_retract z δ x = x := by
  have hn : ‖x - z‖ ≤ δ := (mem_ball_iff_norm.mp hx).le
  simp [b65_retract, max_eq_left hn, hδ.ne', add_sub_cancel]

theorem b65_parameter_integral_analytic_mathlib (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (P : Type*) [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    (f : ℝ × P → E) (U : Set P) (a b : ℝ) (hU : IsOpen U)
    (hc : ContinuousOn f (uIcc a b ×ˢ U))
    (hf : ∀ t ∈ uIcc a b, AnalyticOnNhd ℂ (fun z ↦ f (t, z)) U) :
    AnalyticOnNhd ℂ (fun z ↦ ∫ t in a..b, f (t, z)) U := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  letI : MeasurableSpace P := borel P
  letI : BorelSpace P := ⟨rfl⟩
  intro z hz
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU z hz
  let δ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsub : closedBall z (2 * δ) ⊆ U :=
    (closedBall_subset_ball (by dsimp [δ]; linarith)).trans hεU
  have hsub' : closedBall z δ ⊆ U :=
    (closedBall_subset_closedBall (by linarith)).trans hsub
  let c : ℝ → ℝ := fun t ↦ max (min a b) (min (max a b) t)
  have hcc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hcI : ∀ t, c t ∈ uIcc a b := by
    intro t
    exact ⟨le_max_left _ _, max_le min_le_max (min_le_left _ _)⟩
  have hcEq : ∀ t ∈ uIcc a b, c t = t := by
    intro t ht
    simp only [c, min_eq_right ht.2, max_eq_right ht.1]
  let g : ℝ × P → E := fun q ↦ f (c q.1, b65_retract z δ q.2)
  have hg : Continuous g := hc.comp_continuous
    ((hcc.comp continuous_fst).prodMk ((b65_retract_continuous z hδ).comp continuous_snd))
    (fun q ↦ ⟨hcI q.1, hsub' (b65_retract_mem z hδ q.2)⟩)
  have hgeq (t : ℝ) (ht : t ∈ uIcc a b) (x : P) (hx : x ∈ ball z δ) :
      g (t, x) = f (t, x) := by
    dsimp [g]
    rw [hcEq t ht, b65_retract_eq z hδ hx]
  have hdeq (t : ℝ) (ht : t ∈ uIcc a b) (x : P) (hx : x ∈ ball z δ) :
      fderiv ℂ (fun v ↦ g (t, v)) x = fderiv ℂ (fun v ↦ f (t, v)) x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [isOpen_ball.mem_nhds hx] with v hv
    exact hgeq t ht v hv
  have hK : IsCompact (uIcc a b ×ˢ closedBall z (2 * δ)) :=
    isCompact_uIcc.prod (isCompact_closedBall _ _)
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn (hc.mono (prod_mono Subset.rfl hsub))
  let C := max C₀ 0
  have hC (t : ℝ) (ht : t ∈ uIcc a b) (x : P) (hx : x ∈ closedBall z (2 * δ)) :
      ‖f (t, x)‖ ≤ C := (hC₀ (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)
  have hball (x : P) (hx : x ∈ ball z δ) : ball x δ ⊆ closedBall z (2 * δ) := by
    intro v hv
    exact (dist_triangle v x z).trans (by linarith [mem_ball.mp hx, mem_ball.mp hv])
  have hbound (t : ℝ) (ht : t ∈ uIcc a b) (x : P) (hx : x ∈ ball z δ) :
      ‖fderiv ℂ (fun v ↦ f (t, v)) x‖ ≤ 2 * C / δ := by
    apply Complex.norm_fderiv_le_div_of_mapsTo_ball
      ((hf t ht).differentiableOn.mono ((hball x hx).trans hsub)) _ hδ
    intro v hv
    rw [mem_closedBall, dist_eq_norm]
    calc
      ‖f (t, v) - f (t, x)‖ ≤ ‖f (t, v)‖ + ‖f (t, x)‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hC t ht v (hball x hx hv))
        (hC t ht x ((hball x hx) (mem_ball_self hδ)))
      _ = 2 * C := by ring
  have hcont (x : P) (hx : x ∈ ball z δ) : ContinuousOn (fun t ↦ f (t, x)) (uIcc a b) :=
    hc.comp (continuousOn_id.prodMk continuousOn_const)
      (fun t ht ↦ ⟨ht, hsub' (ball_subset_closedBall hx)⟩)
  have hdiff : DifferentiableOn ℂ (fun x ↦ ∫ t in a..b, f (t, x)) (ball z δ) := by
    intro x hx
    refine HasFDerivAt.differentiableAt (f' := ∫ t in a..b,
      fderiv ℂ (fun v ↦ f (t, v)) x) ?_ |>.differentiableWithinAt
    apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (𝕜 := ℂ) (μ := volume) (F := fun x t ↦ f (t, x))
      (F' := fun x t ↦ fderiv ℂ (fun v ↦ f (t, v)) x)
      (bound := fun _ ↦ 2 * C / δ) (isOpen_ball.mem_nhds hx)
    · filter_upwards [isOpen_ball.mem_nhds hx] with v hv
      exact ((hcont v hv).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
    · exact (hcont x hx).intervalIntegrable
    · have hm : Measurable (fun t : ℝ ↦ fderiv ℂ (fun v ↦ g (t, v)) x) :=
        (measurable_fderiv_with_param ℂ (f := fun t v ↦ g (t, v)) hg).comp
        (measurable_id.prodMk measurable_const)
      apply hm.aestronglyMeasurable.congr
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      exact hdeq t (uIoc_subset_uIcc ht) x hx
    · exact Eventually.of_forall fun t ht v hv ↦ hbound t (uIoc_subset_uIcc ht) v hv
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun t ht v hv ↦
        (hf t (uIoc_subset_uIcc ht) v (hsub' (ball_subset_closedBall hv))).differentiableAt.hasFDerivAt
  exact b65_spec_analyticOnNhd_of_differentiableOn_aux isOpen_ball hdiff z (mem_ball_self hδ)

end HodgeLean.Foundations.Program
