import HodgeLean.Foundations.Program.SchoenTowerL1bActionSourceAsymptotics

noncomputable section
set_option maxHeartbeats 200000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- A selected logarithmic lift is continuous sufficiently far toward the
puncture when its underlying germ is continuous near zero. -/
theorem s2v_l1b_action_sourceLift_eventually_continuousAt
    (f : ℂ → ℂ) (a : ℂ) (hfzero : f 0 = 0)
    (hf : HasDerivAt f (Complex.exp a) 0)
    (hc : ∀ᶠ z : ℂ in 𝓝 0, ContinuousAt f z) :
    ∀ᶠ w : ℂ in comap Complex.re atBot,
      ContinuousAt (s2v_l1b_action_sourceLift f a) w := by
  have he : Tendsto Complex.exp (comap Complex.re atBot) (𝓝[≠] (0 : ℂ)) := by
    change map Complex.exp (comap Complex.re atBot) ≤ 𝓝[≠] (0 : ℂ)
    rw [Complex.map_exp_comap_re_atBot]
  have hslit := (s2v_l1b_action_source_normalized_ratio_tendsto f a hfzero hf).eventually
    (Complex.isOpen_slitPlane.mem_nhds (by simp : (1 : ℂ) ∈ Complex.slitPlane))
  filter_upwards [(he.mono_right nhdsWithin_le_nhds).eventually hc, he.eventually hslit]
    with w hfw hsw
  have hr : ContinuousAt (fun z => f (Complex.exp z) / (Complex.exp a * Complex.exp z)) w :=
    (hfw.comp Complex.continuous_exp.continuousAt).div
      (continuous_const.mul Complex.continuous_exp).continuousAt
      (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
  change ContinuousAt (fun z => z + a + Complex.log
    (f (Complex.exp z) / (Complex.exp a * Complex.exp z))) w
  have hlog : ContinuousAt (fun z => Complex.log
      (f (Complex.exp z) / (Complex.exp a * Complex.exp z))) w := by
    simpa only [Function.comp_def] using ContinuousAt.comp
      (f := fun z => f (Complex.exp z) / (Complex.exp a * Complex.exp z))
      (g := Complex.log) (continuousAt_clog hsw) hr
  exact (continuous_id.add continuous_const).continuousAt.add hlog

end HodgeLean.Foundations.Program
