import HodgeLean.Foundations.Program.FuchsianSystemDisc
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

noncomputable section
open Set Metric Filter Topology
namespace HodgeLean.Foundations.Program

theorem b65f_uniform_clm_apply {X E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {U : Set X} {f : ℕ → X → E} {g : X → E} {A : X → E →L[ℂ] F} {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ x ∈ U, ‖A x‖ ≤ C) (hg : TendstoUniformlyOn f g atTop U) :
    TendstoUniformlyOn (fun n x ↦ A x (f n x)) (fun x ↦ A x (g x)) atTop U := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hC' : 0 < C + 1 := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hg (ε / (C + 1)) (div_pos hε hC')] with n hn x hx
  calc
    dist (A x (g x)) (A x (f n x)) = ‖A x (g x - f n x)‖ := by rw [dist_eq_norm, map_sub]
    _ ≤ ‖A x‖ * ‖g x - f n x‖ := (A x).le_opNorm _
    _ ≤ (C + 1) * dist (g x) (f n x) := by
      rw [dist_eq_norm]
      exact mul_le_mul_of_nonneg_right ((hA x hx).trans (by linarith)) (norm_nonneg _)
    _ < (C + 1) * (ε / (C + 1)) := mul_lt_mul_of_pos_left (hn x hx) hC'
    _ = ε := by field_simp


theorem b65f_linearPartial_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {A : ℂ → E →L[ℂ] E} {c : ℂ} {R : ℝ} (v : E)
    (hA : AnalyticOnNhd ℂ A (ball c R)) :
    ∀ n x, x ∈ ball c R → HasDerivAt
      (fun t ↦ ∑ i ∈ Finset.range (n + 1), b65f_linearTerm A c v i t)
      (A x (∑ i ∈ Finset.range n, b65f_linearTerm A c v i x)) x := by
  intro n
  induction n with
  | zero =>
    intro x hx
    simpa [b65f_linearTerm] using hasDerivAt_const x v
  | succ n ih =>
    intro x hx
    have hh := b65f_segmentPrimitive_hasDerivAt
      (hA.differentiableOn.clm_apply (b65f_linearTerm_analytic v hA n).differentiableOn) hx
    have ht : HasDerivAt (b65f_linearTerm A c v (n + 1))
        (A x (b65f_linearTerm A c v n x)) x := hh
    convert (ih x hx).add ht using 1
    · funext t
      simp only [Pi.add_apply, Finset.sum_range_succ]
    · simp only [Finset.sum_range_succ, map_add]


def b65f_leftCoefficient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ℂ → E →L[ℂ] E) (w : ℂ) : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) :=
  ContinuousLinearMap.mul ℂ (E →L[ℂ] E) (A w)

theorem b65f_leftCoefficient_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : ℂ → E →L[ℂ] E} {U : Set ℂ} (hA : AnalyticOnNhd ℂ A U) :
    AnalyticOnNhd ℂ (b65f_leftCoefficient A) U := by
  intro w hw
  exact ((ContinuousLinearMap.mul ℂ (E →L[ℂ] E)).analyticAt (A w)).comp (hA w hw)

theorem b65f_segment_eq_series {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {A : ℂ → E →L[ℂ] E} {a z : ℂ} {r : ℝ}
    (hA : AnalyticOnNhd ℂ A (ball a r)) (hz : z ∈ ball a r) :
    b65f_segment E A a z = ∑' m, b65f_linearTerm (b65f_leftCoefficient A) a 1 m z := by
  apply tsum_congr
  intro m
  change b65f_iterated E A a z m 1 = b65f_linearTerm
    (fun w ↦ ContinuousLinearMap.mul ℂ (E →L[ℂ] E) (A w)) a 1 m z
  simpa using b65f_iterated_eq_linearTerm E A a r hA z hz m 1 ⟨zero_le_one, le_rfl⟩

theorem b65f_operatorSeries_uniform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {A : ℂ → E →L[ℂ] E} {a : ℂ} {r C : ℝ}
    (hA : AnalyticOnNhd ℂ A (ball a r)) (hC : 0 ≤ C)
    (hb : ∀ z ∈ ball a r, ‖A z‖ ≤ C) :
    TendstoUniformlyOn (fun n z ↦ ∑ m ∈ Finset.range n,
        b65f_linearTerm (b65f_leftCoefficient A) a 1 m z)
      (fun z ↦ ∑' m, b65f_linearTerm (b65f_leftCoefficient A) a 1 m z) atTop (ball a r) := by
  apply tendstoUniformlyOn_tsum_nat (Real.summable_pow_div_factorial (r * C))
  intro m z hz
  have hbound := b65f_iterated_norm_le E A a z C hC
    (fun t ht ↦ hb _ (b65f_segment_mem_ball hz ht)) m 1 ⟨zero_le_one, le_rfl⟩
  rw [b65f_iterated_eq_linearTerm E A a r hA z hz m 1 ⟨zero_le_one, le_rfl⟩] at hbound
  simp only [Complex.ofReal_one, one_mul, add_sub_cancel, one_pow, mul_one] at hbound
  apply hbound.trans
  gcongr
  exact (mem_ball_iff_norm.mp hz).le

theorem b65f_segment_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {A : ℂ → E →L[ℂ] E} {a : ℂ} {R : ℝ}
    (hA : AnalyticOnNhd ℂ A (ball a R)) {x : ℂ} (hx : x ∈ ball a R) :
    HasDerivAt (b65f_segment E A a) (A x * b65f_segment E A a x) x := by
  let L := b65f_leftCoefficient A
  let Y := fun z ↦ ∑' m, b65f_linearTerm L a 1 m z
  have hL : AnalyticOnNhd ℂ L (ball a R) := b65f_leftCoefficient_analytic hA
  have heq : Set.EqOn (b65f_segment E A a) Y (ball a R) := fun z hz ↦ b65f_segment_eq_series hA hz
  obtain ⟨r, hxr, hrR⟩ := exists_between (mem_ball.mp hx)
  have hr : 0 < r := (dist_nonneg (x := x) (y := a)).trans_lt hxr
  have hsub : closedBall a r ⊆ ball a R := closedBall_subset_ball hrR
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall a r).exists_bound_of_continuousOn (hA.continuousOn.mono hsub)
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hb : ∀ z ∈ ball a r, ‖A z‖ ≤ C :=
    fun z hz ↦ (hC₀ z (ball_subset_closedBall hz)).trans (le_max_left _ _)
  have ht := b65f_operatorSeries_uniform (hA.mono (ball_subset_ball hrR.le)) hC hb
  have ht' := b65f_uniform_clm_apply hC
    (show ∀ z ∈ ball a r, ‖L z‖ ≤ C from fun z hz ↦
      (ContinuousLinearMap.opNorm_mul_apply_le ℂ (E →L[ℂ] E) (A z)).trans (hb z hz)) ht
  have hd : HasDerivAt Y (L x (Y x)) x := by
    apply hasDerivAt_of_tendstoUniformlyOn isOpen_ball ht'
      (f := fun n z ↦ ∑ m ∈ Finset.range (n + 1), b65f_linearTerm L a 1 m z)
    · exact Eventually.of_forall fun n z hz ↦
        b65f_linearPartial_hasDerivAt 1 hL n z (ball_subset_ball hrR.le hz)
    · intro z hz
      exact (ht.tendsto_at hz).comp (tendsto_add_atTop_nat 1)
    · exact hxr
  rw [heq hx]
  change HasDerivAt (b65f_segment E A a) (L x (Y x)) x
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds hx] with z hz
  exact heq hz

end HodgeLean.Foundations.Program
