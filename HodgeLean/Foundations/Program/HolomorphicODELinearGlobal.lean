import HodgeLean.Foundations.Program.HolomorphicODELinear

noncomputable section
open Set Metric Filter Topology
namespace HodgeLean.Foundations.Program

def b65_linearSeries {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ℂ → E →L[ℂ] E) (c : ℂ) (v : E) (x : ℂ) : E :=
  ∑' n, b65_linearTerm A c v n x

theorem b65_linearSeries_uniform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {A : ℂ → E →L[ℂ] E} {c : ℂ} {r C : ℝ} (v : E)
    (hr : 0 < r) (hC : 0 ≤ C) (hb : ∀ x ∈ ball c r, ‖A x‖ ≤ C) :
    TendstoUniformlyOn (fun n x ↦ ∑ i ∈ Finset.range n, b65_linearTerm A c v i x)
      (b65_linearSeries A c v) atTop (ball c r) := by
  apply tendstoUniformlyOn_tsum_nat ((Real.summable_pow_div_factorial (C * r)).mul_left ‖v‖)
  intro n x hx
  apply (b65_linearTerm_bound hC v hb n x hx).trans
  calc
    ‖v‖ * C ^ n * ‖x - c‖ ^ n / n.factorial ≤ ‖v‖ * C ^ n * r ^ n / n.factorial := by
      gcongr
      exact (mem_ball_iff_norm.mp hx).le
    _ = ‖v‖ * ((C * r) ^ n / n.factorial) := by rw [mul_pow]; ring

theorem b65_linearSeries_initial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ℂ → E →L[ℂ] E) (c : ℂ) (v : E) : b65_linearSeries A c v c = v := by
  unfold b65_linearSeries
  rw [tsum_eq_single 0]
  · rfl
  · intro n hn
    cases n with
    | zero => exact (hn rfl).elim
    | succ n => simp [b65_linearTerm, b65_segmentPrimitive]

theorem b65_global_linear_solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {A : ℂ → E →L[ℂ] E} {c : ℂ} {R : ℝ}
    (v : E) (hA : AnalyticOnNhd ℂ A (ball c R)) :
    ∃ Y : ℂ → E, AnalyticOnNhd ℂ Y (ball c R) ∧ Y c = v ∧
      ∀ x ∈ ball c R, HasDerivAt Y (A x (Y x)) x := by
  have hd : ∀ x ∈ ball c R, HasDerivAt (b65_linearSeries A c v)
      (A x (b65_linearSeries A c v x)) x := by
    intro x hx
    obtain ⟨r, hxr, hrR⟩ := exists_between (mem_ball.mp hx)
    have hr : 0 < r := (dist_nonneg (x := x) (y := c)).trans_lt hxr
    have hsub : closedBall c r ⊆ ball c R := closedBall_subset_ball hrR
    obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn (hA.continuousOn.mono hsub)
    let C := max C₀ 0
    have hC : 0 ≤ C := le_max_right _ _
    have hb : ∀ z ∈ ball c r, ‖A z‖ ≤ C :=
      fun z hz ↦ (hC₀ z (ball_subset_closedBall hz)).trans (le_max_left _ _)
    have ht := b65_linearSeries_uniform v hr hC hb
    have ht' := b65_uniform_clm_apply hC hb ht
    apply hasDerivAt_of_tendstoUniformlyOn isOpen_ball ht'
      (f := fun n t ↦ ∑ i ∈ Finset.range (n + 1), b65_linearTerm A c v i t)
    · exact Eventually.of_forall fun n z hz ↦
        b65_linearPartial_hasDerivAt v hA n z (ball_subset_ball hrR.le hz)
    · intro z hz
      exact (ht.tendsto_at hz).comp (tendsto_add_atTop_nat 1)
    · exact hxr
  refine ⟨b65_linearSeries A c v, ?_, b65_linearSeries_initial A c v, hd⟩
  exact (show DifferentiableOn ℂ (b65_linearSeries A c v) (ball c R) from
    fun x hx ↦ (hd x hx).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball

end HodgeLean.Foundations.Program
