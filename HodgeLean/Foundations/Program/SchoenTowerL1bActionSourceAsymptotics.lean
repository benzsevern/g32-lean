import HodgeLean.Foundations.Program.SchoenTowerL1bActionSourceLift

noncomputable section
set_option maxHeartbeats 200000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- Along the covering half-plane toward the puncture, the chosen source
lift differs from its tangent translation by a term tending to zero. -/
theorem s2v_l1b_action_sourceLift_error_tendsto
    (f : ℂ → ℂ) (a : ℂ) (hfzero : f 0 = 0)
    (hf : HasDerivAt f (Complex.exp a) 0) :
    Tendsto (fun w => s2v_l1b_action_sourceLift f a w - w - a)
      (comap Complex.re atBot) (𝓝 0) := by
  have he : Tendsto Complex.exp (comap Complex.re atBot) (𝓝[≠] (0 : ℂ)) := by
    change map Complex.exp (comap Complex.re atBot) ≤ 𝓝[≠] (0 : ℂ)
    rw [Complex.map_exp_comap_re_atBot]
  have ht := (s2v_l1b_action_source_log_correction_tendsto f a hfzero hf).comp he
  convert ht using 1
  funext w
  dsimp [s2v_l1b_action_sourceLift]
  ring

/-- The selected source lift preserves the end of the covering plane
corresponding to the source puncture. -/
theorem s2v_l1b_action_sourceLift_tendsto_left
    (f : ℂ → ℂ) (a : ℂ) (hfzero : f 0 = 0)
    (hf : HasDerivAt f (Complex.exp a) 0) :
    Tendsto (s2v_l1b_action_sourceLift f a) (comap Complex.re atBot)
      (comap Complex.re atBot) := by
  have he := s2v_l1b_action_sourceLift_error_tendsto f a hfzero hf
  have heR := (Complex.continuous_re.tendsto (0 : ℂ)).comp he
  have hh := (tendsto_comap : Tendsto Complex.re (comap Complex.re atBot) atBot).atBot_add
    (heR.add_const a.re)
  apply tendsto_comap_iff.mpr
  convert hh using 1
  funext w
  simp only [Function.comp_apply, Complex.sub_re]
  ring

end HodgeLean.Foundations.Program
