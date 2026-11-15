import HodgeLean.Foundations.Program.SchoenTowerL1bActionHalfPlaneLift

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- An eventual condition at the covering-plane end holds on an entire
sufficiently small left half-plane. -/
theorem s2v_l1b_action_left_end_cutoff
    (P : ℂ → Prop) (hP : ∀ᶠ z in comap Complex.re atBot, P z) :
    ∃ b : ℝ, ∀ z : ℂ, z.re < b → P z := by
  obtain ⟨b, hb⟩ := eventually_atBot.mp (eventually_comap.mp hP)
  exact ⟨b, fun z hz => hb z.re (le_of_lt hz) z rfl⟩

/-- Two logarithmic representatives continuous sufficiently far toward
the puncture and with equal exponential projections differ by one
constant integral deck translation on a smaller half-plane. -/
theorem s2v_l1b_action_end_log_lifts_differ_int
    (F G : ℂ → ℂ)
    (hF : ∀ᶠ z in comap Complex.re atBot, ContinuousAt F z)
    (hG : ∀ᶠ z in comap Complex.re atBot, ContinuousAt G z)
    (he : ∀ᶠ z in comap Complex.re atBot, Complex.exp (F z) = Complex.exp (G z)) :
    ∃ k : ℤ, ∀ᶠ z in comap Complex.re atBot,
      F z = G z + (k : ℂ) * (2 * Real.pi * Complex.I) := by
  obtain ⟨b, hb⟩ := s2v_l1b_action_left_end_cutoff
    (fun z => ContinuousAt F z ∧ ContinuousAt G z ∧ Complex.exp (F z) = Complex.exp (G z))
    (hF.and (hG.and he))
  let X := {z : ℂ // z.re < b}
  haveI : PreconnectedSpace X := Subtype.preconnectedSpace (convex_halfSpace_re_lt b).isPreconnected
  have hf : Continuous (fun z : X => F z) := continuous_iff_continuousAt.mpr
    (fun z => ((hb z z.property).1).comp continuous_subtype_val.continuousAt)
  have hg : Continuous (fun z : X => G z) := continuous_iff_continuousAt.mpr
    (fun z => ((hb z z.property).2.1).comp continuous_subtype_val.continuousAt)
  let z₀ : X := ⟨((b - 1 : ℝ) : ℂ), by
    change b - 1 < b
    linarith⟩
  obtain ⟨k, hk⟩ := s2v_l1b_action_log_lifts_differ_int
    (fun z : X => F z) (fun z : X => G z) hf hg (fun z => (hb z z.property).2.2) z₀
  refine ⟨k, ?_⟩
  filter_upwards [(tendsto_comap : Tendsto Complex.re (comap Complex.re atBot) atBot).eventually
    (eventually_lt_atBot b)] with z hz
  exact hk ⟨z, hz⟩

/-- Continuity on a covering half-plane gives continuity at every point
sufficiently far toward its puncture end. -/
theorem s2v_l1b_action_halfplane_eventually_continuousAt
    (L : ℂ → ℂ) (b : ℝ) (hL : ContinuousOn L {z : ℂ | z.re < b}) :
    ∀ᶠ z : ℂ in comap Complex.re atBot, ContinuousAt L z := by
  filter_upwards [(tendsto_comap : Tendsto Complex.re (comap Complex.re atBot) atBot).eventually
    (eventually_lt_atBot b)] with z hz
  exact hL.continuousAt ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds hz)

end HodgeLean.Foundations.Program
