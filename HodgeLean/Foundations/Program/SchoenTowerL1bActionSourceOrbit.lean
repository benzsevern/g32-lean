import HodgeLean.Foundations.Program.SchoenTowerL1bActionSourceAsymptotics
import HodgeLean.Foundations.Program.SchoenTowerL1bActionOrbitError

noncomputable section
set_option maxHeartbeats 200000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- All steps of any fixed finite source-lift orbit have angular error
uniformly tending to zero toward the puncture. -/
theorem s2v_l1b_action_sourceLift_orbit_angular_error
    (f : ℂ → ℂ) (a : ℂ) (hfzero : f 0 = 0)
    (hf : HasDerivAt f (Complex.exp a) 0) (N : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ w : ℂ in comap Complex.re atBot, ∀ j < N,
      |((s2v_l1b_action_sourceLift f a)^[j + 1] w -
        (s2v_l1b_action_sourceLift f a)^[j] w).im - a.im| < δ := by
  let F := s2v_l1b_action_sourceLift f a
  have he := s2v_l1b_action_sourceLift_error_tendsto f a hfzero hf
  have hleft := s2v_l1b_action_sourceLift_tendsto_left f a hfzero hf
  have hj (j : Fin N) : ∀ᶠ w : ℂ in comap Complex.re atBot,
      |(F^[j.val + 1] w - F^[j.val] w).im - a.im| < δ := by
    have ht := he.comp (hleft.iterate j.val)
    have hb := ht (Metric.ball_mem_nhds (0 : ℂ) hδ)
    filter_upwards [hb] with w hw
    have hn : ‖F (F^[j.val] w) - F^[j.val] w - a‖ < δ := by
      simpa only [Set.mem_preimage, Function.comp_def, Metric.mem_ball, dist_zero_right, F] using hw
    have hi := (Complex.abs_im_le_norm (F (F^[j.val] w) - F^[j.val] w - a)).trans_lt hn
    simpa only [Function.iterate_succ_apply', Complex.sub_im] using hi
  filter_upwards [Filter.eventually_all.mpr hj] with w hw j hjN
  exact hw ⟨j, hjN⟩

/-- Every fixed finite iterate of the selected source lift projects to the
corresponding actual source iterate sufficiently near the puncture. -/
theorem s2v_l1b_action_sourceLift_iterate_exp_eventually
    (f : ℂ → ℂ) (a : ℂ) (hfzero : f 0 = 0)
    (hf : HasDerivAt f (Complex.exp a) 0) (n : ℕ) :
    ∀ᶠ w : ℂ in comap Complex.re atBot,
      Complex.exp ((s2v_l1b_action_sourceLift f a)^[n] w) = f^[n] (Complex.exp w) := by
  have hleft := s2v_l1b_action_sourceLift_tendsto_left f a hfzero hf
  have he : Tendsto Complex.exp (comap Complex.re atBot) (𝓝[≠] (0 : ℂ)) := by
    change map Complex.exp (comap Complex.re atBot) ≤ 𝓝[≠] (0 : ℂ)
    rw [Complex.map_exp_comap_re_atBot]
  have hn := s2v_l1b_action_source_eventually_ne_zero f a hfzero hf
  induction n with
  | zero => exact Eventually.of_forall (fun _ => rfl)
  | succ n ih =>
    have hne := (he.comp (hleft.iterate n)).eventually hn
    filter_upwards [ih, hne] with w hw hnw
    change f (Complex.exp ((s2v_l1b_action_sourceLift f a)^[n] w)) ≠ 0 at hnw
    rw [Function.iterate_succ_apply', s2v_l1b_action_sourceLift_exp _ _ _ hnw,
      hw, Function.iterate_succ_apply']

/-- A locally periodic source germ with the prescribed tangent angle has
positive primitive deck return in its selected logarithmic lift. -/
theorem s2v_l1b_action_sourceLift_primitive_return
    (f : ℂ → ℂ) (a : ℂ) (hfzero : f 0 = 0)
    (hf : HasDerivAt f (Complex.exp a) 0) (N : ℕ) (hN : 0 < N)
    (ha : a.im = (2 * Real.pi) / N)
    (hperiod : ∀ᶠ z : ℂ in 𝓝 0, f^[N] z = z) :
    ∀ᶠ w : ℂ in comap Complex.re atBot,
      (s2v_l1b_action_sourceLift f a)^[N] w = w + 2 * Real.pi * Complex.I := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hstep := s2v_l1b_action_sourceLift_orbit_angular_error f a hfzero hf N
    ((2 * Real.pi) / N) (div_pos Real.two_pi_pos hNr)
  have hproj := s2v_l1b_action_sourceLift_iterate_exp_eventually f a hfzero hf N
  have he : Tendsto Complex.exp (comap Complex.re atBot) (𝓝[≠] (0 : ℂ)) := by
    change map Complex.exp (comap Complex.re atBot) ≤ 𝓝[≠] (0 : ℂ)
    rw [Complex.map_exp_comap_re_atBot]
  have hp := (he.mono_right nhdsWithin_le_nhds).eventually hperiod
  filter_upwards [hstep, hproj, hp] with w hstepw hprojw hpw
  apply s2v_l1b_action_primitive_return_of_orbit_error _ N hN w (hprojw.trans hpw)
  intro j hj
  simpa only [ha] using hstepw j hj

end HodgeLean.Foundations.Program
