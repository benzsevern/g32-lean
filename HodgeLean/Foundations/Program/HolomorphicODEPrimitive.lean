import HodgeLean.Foundations.Program.HolomorphicODEIntegral

noncomputable section
open Set Metric Filter Topology MeasureTheory
open scoped Interval
namespace HodgeLean.Foundations.Program

def b65_segmentPrimitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (c x : ℂ) : E :=
  (x - c) • ∫ t in (0 : ℝ)..1, f (c + (t : ℂ) * (x - c))

theorem b65_segment_mem_ball {c x : ℂ} {r : ℝ} (hx : x ∈ ball c r)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : c + (t : ℂ) * (x - c) ∈ ball c r := by
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt (mem_ball_iff_norm.mp hx)

theorem b65_segmentPrimitive_hasDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {c : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (ball c r)) {x : ℂ} (hx : x ∈ ball c r) :
    HasDerivAt (b65_segmentPrimitive f c) (f x) x := by
  obtain ⟨g, hg⟩ := hf.isExactOn_ball
  have heq (v : ℂ) (hv : v ∈ ball c r) : b65_segmentPrimitive f c v = g v - g c := by
    have hline : Continuous (fun t : ℝ ↦ c + (t : ℂ) * (v - c)) := by fun_prop
    have hcont : ContinuousOn (fun t : ℝ ↦ f (c + (t : ℂ) * (v - c))) (uIcc (0 : ℝ) 1) := by
      apply hf.continuousOn.comp hline.continuousOn
      intro t ht
      exact b65_segment_mem_ball hv (by simpa using ht)
    have hder : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ ↦ g (c + (t : ℂ) * (v - c)))
          ((v - c) • f (c + (t : ℂ) * (v - c))) t := by
      intro t ht
      have hm := b65_segment_mem_ball hv (by simpa using ht)
      simpa [Function.comp_def] using (hg _ hm).scomp t
        ((Complex.ofRealCLM.hasDerivAt.mul_const (v - c)).const_add c)
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hder
      ((continuousOn_const.smul hcont).intervalIntegrable)
    simpa [b65_segmentPrimitive, intervalIntegral.integral_smul] using hi
  apply ((hg x hx).sub_const (g c)).congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds hx] with v hv
  exact heq v hv

theorem b65_segmentPrimitive_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℂ → E} {c x : ℂ} {r M : ℝ}
    (hx : x ∈ ball c r) (hb : ∀ v ∈ ball c r, ‖f v‖ ≤ M) :
    ‖b65_segmentPrimitive f c x‖ ≤ ‖x - c‖ * M := by
  rw [b65_segmentPrimitive, norm_smul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := fun t ↦ f (c + (t : ℂ) * (x - c)))
    (fun t ht ↦ hb _ (b65_segment_mem_ball hx (by simpa using uIoc_subset_uIcc ht)))
  simpa using hi

theorem b65_segmentPrimitive_analytic_parameters
    {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    {A : P × ℂ → E} {U : Set P} {c : ℂ} {r : ℝ} (hU : IsOpen U)
    (hA : AnalyticOnNhd ℂ A (U ×ˢ ball c r)) :
    AnalyticOnNhd ℂ (fun q : P × ℂ ↦ b65_segmentPrimitive (fun x ↦ A (q.1, x)) c q.2)
      (U ×ˢ ball c r) := by
  let f : ℝ × (P × ℂ) → E := fun q ↦ A (q.2.1, c + (q.1 : ℂ) * (q.2.2 - c))
  have hm : ∀ q ∈ uIcc (0 : ℝ) 1 ×ˢ (U ×ˢ ball c r),
      (q.2.1, c + (q.1 : ℂ) * (q.2.2 - c)) ∈ U ×ˢ ball c r := by
    intro q hq
    exact ⟨hq.2.1, b65_segment_mem_ball hq.2.2 (by simpa using hq.1)⟩
  have hc : ContinuousOn f (uIcc (0 : ℝ) 1 ×ˢ (U ×ˢ ball c r)) := by
    exact hA.continuousOn.comp (show Continuous (fun q : ℝ × (P × ℂ) ↦
      (q.2.1, c + (q.1 : ℂ) * (q.2.2 - c))) from by fun_prop).continuousOn hm
  have hf : ∀ t ∈ uIcc (0 : ℝ) 1, AnalyticOnNhd ℂ (fun q ↦ f (t, q)) (U ×ˢ ball c r) := by
    intro t ht q hq
    apply (hA _ (hm (t, q) ⟨ht, hq⟩)).comp₂
      (analyticAt_fst : AnalyticAt ℂ (fun q : P × ℂ ↦ q.1) q)
    have hsub : AnalyticAt ℂ (fun q : P × ℂ ↦ q.2 - c) q :=
      analyticAt_snd.sub analyticAt_const
    have hmul := (analyticAt_const : AnalyticAt ℂ (fun _ : P × ℂ ↦ (t : ℂ)) q).mul hsub
    exact (analyticAt_const : AnalyticAt ℂ (fun _ : P × ℂ ↦ c) q).add hmul
  have hi := b65_parameter_integral_analytic_mathlib E (P × ℂ) f
    (U ×ˢ ball c r) 0 1 (hU.prod isOpen_ball) hc hf
  intro q hq
  exact (analyticAt_snd.sub analyticAt_const).smul (hi q hq)

end HodgeLean.Foundations.Program
