import HodgeLean.Foundations.Program.FuchsianSystemSeries
import Mathlib.Analysis.Complex.HasPrimitives

noncomputable section
open Set Metric Filter Topology MeasureTheory
open scoped Interval
namespace HodgeLean.Foundations.Program

def b65f_segmentPrimitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (c x : ℂ) : E :=
  (x - c) • ∫ t in (0 : ℝ)..1, f (c + (t : ℂ) * (x - c))

theorem b65f_segment_mem_ball {c x : ℂ} {r : ℝ} (hx : x ∈ ball c r)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : c + (t : ℂ) * (x - c) ∈ ball c r := by
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt (mem_ball_iff_norm.mp hx)

theorem b65f_segmentPrimitive_hasDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {c : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (ball c r)) {x : ℂ} (hx : x ∈ ball c r) :
    HasDerivAt (b65f_segmentPrimitive f c) (f x) x := by
  obtain ⟨g, hg⟩ := hf.isExactOn_ball
  have heq (v : ℂ) (hv : v ∈ ball c r) : b65f_segmentPrimitive f c v = g v - g c := by
    have hline : Continuous (fun t : ℝ ↦ c + (t : ℂ) * (v - c)) := by fun_prop
    have hcont : ContinuousOn (fun t : ℝ ↦ f (c + (t : ℂ) * (v - c))) (uIcc (0 : ℝ) 1) := by
      apply hf.continuousOn.comp hline.continuousOn
      intro t ht
      exact b65f_segment_mem_ball hv (by simpa using ht)
    have hder : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ ↦ g (c + (t : ℂ) * (v - c)))
          ((v - c) • f (c + (t : ℂ) * (v - c))) t := by
      intro t ht
      have hm := b65f_segment_mem_ball hv (by simpa using ht)
      simpa [Function.comp_def] using (hg _ hm).scomp t
        ((Complex.ofRealCLM.hasDerivAt.mul_const (v - c)).const_add c)
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hder
      ((continuousOn_const.smul hcont).intervalIntegrable)
    simpa [b65f_segmentPrimitive, intervalIntegral.integral_smul] using hi
  apply ((hg x hx).sub_const (g c)).congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds hx] with v hv
  exact heq v hv

def b65f_linearTerm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ℂ → E →L[ℂ] E) (c : ℂ) (v : E) : ℕ → ℂ → E
  | 0 => fun _ ↦ v
  | n + 1 => b65f_segmentPrimitive (fun x ↦ A x (b65f_linearTerm A c v n x)) c

theorem b65f_linearTerm_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {A : ℂ → E →L[ℂ] E} {c : ℂ} {R : ℝ} (v : E)
    (hA : AnalyticOnNhd ℂ A (ball c R)) :
    ∀ n, AnalyticOnNhd ℂ (b65f_linearTerm A c v n) (ball c R) := by
  intro n
  induction n with
  | zero => exact fun x hx ↦ analyticAt_const
  | succ n ih =>
    have hd := hA.differentiableOn.clm_apply ih.differentiableOn
    apply DifferentiableOn.analyticOnNhd _ isOpen_ball
    intro x hx
    exact (b65f_segmentPrimitive_hasDerivAt hd hx).differentiableAt.differentiableWithinAt


theorem b65f_iterated_eq_linearTerm (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E]
    (A : ℂ → E →L[ℂ] E) (a : ℂ) (r : ℝ)
    (hA : AnalyticOnNhd ℂ A (ball a r)) (z : ℂ) (hz : z ∈ ball a r)
    (m : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    b65f_iterated E A a z m t =
      b65f_linearTerm (fun w ↦ ContinuousLinearMap.mul ℂ (E →L[ℂ] E) (A w)) a 1 m
        (a + (t : ℂ) * (z - a)) := by
  induction m generalizing t with
  | zero => rfl
  | succ m ih =>
    let L : ℂ → (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) :=
      fun w ↦ ContinuousLinearMap.mul ℂ (E →L[ℂ] E) (A w)
    have hL : AnalyticOnNhd ℂ L (ball a r) := by
      intro w hw
      exact ((ContinuousLinearMap.mul ℂ (E →L[ℂ] E)).analyticAt (A w)).comp (hA w hw)
    have hd (w : ℂ) (hw : w ∈ ball a r) := b65f_segmentPrimitive_hasDerivAt
      (hL.differentiableOn.clm_apply (b65f_linearTerm_analytic 1 hL m).differentiableOn) hw
    have hcont : ContinuousOn
        (fun q : ℝ ↦ (z - a) • (A (a + (q : ℂ) * (z - a)) *
          b65f_linearTerm L a 1 m (a + (q : ℂ) * (z - a)))) (uIcc 0 t) := by
      have hAc : ContinuousOn (fun q : ℝ ↦ A (a + (q : ℂ) * (z - a))) (uIcc 0 t) := by
        apply hA.continuousOn.comp (by fun_prop)
        intro q hq
        exact b65f_segment_mem_ball hz
          ⟨(uIcc_of_le ht.1 ▸ hq).1, (uIcc_of_le ht.1 ▸ hq).2.trans ht.2⟩
      have hTc : ContinuousOn
          (fun q : ℝ ↦ b65f_linearTerm L a 1 m (a + (q : ℂ) * (z - a))) (uIcc 0 t) := by
        apply (b65f_linearTerm_analytic 1 hL m).continuousOn.comp (by fun_prop)
        intro q hq
        exact b65f_segment_mem_ball hz
          ⟨(uIcc_of_le ht.1 ▸ hq).1, (uIcc_of_le ht.1 ▸ hq).2.trans ht.2⟩
      exact (continuousOn_const : ContinuousOn (fun _ : ℝ ↦ (z - a : ℂ)) (uIcc 0 t)).smul (hAc.mul hTc)
    have hder : ∀ q ∈ uIcc (0 : ℝ) t, HasDerivAt
        (fun q : ℝ ↦ b65f_linearTerm L a 1 (m + 1) (a + (q : ℂ) * (z - a)))
        ((z - a) • (A (a + (q : ℂ) * (z - a)) *
          b65f_linearTerm L a 1 m (a + (q : ℂ) * (z - a)))) q := by
      intro q hq
      have hq' : q ∈ Icc (0 : ℝ) 1 :=
        ⟨(uIcc_of_le ht.1 ▸ hq).1, (uIcc_of_le ht.1 ▸ hq).2.trans ht.2⟩
      simpa [L, Function.comp_def, b65f_linearTerm] using
        (hd _ (b65f_segment_mem_ball hz hq')).scomp q
          ((Complex.ofRealCLM.hasDerivAt.mul_const (z - a)).const_add a)
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hcont.intervalIntegrable
    rw [b65f_iterated]
    have he : (∫ q in (0 : ℝ)..t, (z - a) •
        (A (a + (q : ℂ) * (z - a)) * b65f_iterated E A a z m q)) =
        ∫ q in (0 : ℝ)..t, (z - a) • (A (a + (q : ℂ) * (z - a)) *
          b65f_linearTerm L a 1 m (a + (q : ℂ) * (z - a))) := by
      apply intervalIntegral.integral_congr
      intro q hq
      dsimp only
      rw [ih q ⟨(uIcc_of_le ht.1 ▸ hq).1,
        (uIcc_of_le ht.1 ▸ hq).2.trans ht.2⟩]
    rw [he, hi]
    simp [b65f_linearTerm, b65f_segmentPrimitive, L]

end HodgeLean.Foundations.Program
