import HodgeLean.Foundations.Program.SchoenTowerL1bActionHalfPlaneLift

noncomputable section
set_option maxHeartbeats 200000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- A logarithmic lift of a continuous germ fixing zero preserves the
covering-plane end over that puncture. -/
theorem s2v_l1b_action_log_lift_tendsto_left
    (h L : ℂ → ℂ) (hc : ContinuousAt h 0) (hz : h 0 = 0) (b : ℝ)
    (he : ∀ z, z.re < b → Complex.exp (L z) = h (Complex.exp z)) :
    Tendsto L (comap Complex.re atBot) (comap Complex.re atBot) := by
  have hexp : Tendsto Complex.exp (comap Complex.re atBot) (𝓝 (0 : ℂ)) := by
    rw [← Complex.comap_exp_nhds_zero]
    exact tendsto_comap
  have ht : Tendsto (fun z => h (Complex.exp z)) (comap Complex.re atBot) (𝓝 (0 : ℂ)) := by
    simpa only [hz, Function.comp_def] using hc.tendsto.comp hexp
  have hb : ∀ᶠ z : ℂ in comap Complex.re atBot, z.re < b :=
    (tendsto_comap : Tendsto Complex.re (comap Complex.re atBot) atBot).eventually
      (eventually_lt_atBot b)
  have hp : (fun z => h (Complex.exp z)) =ᶠ[comap Complex.re atBot]
      (fun z => Complex.exp (L z)) := by
    filter_upwards [hb] with z hz
    exact (he z hz).symm
  apply tendsto_comap_iff.mpr
  exact Complex.tendsto_exp_nhds_zero_iff.mp (ht.congr' hp)

end HodgeLean.Foundations.Program
