import HodgeLean.Adapters.NormalConeB4aGysinBallRetraction
import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section
namespace HodgeLean.Adapters
open scoped Topology

/-- A local analytic map has a global continuous extension agreeing with it on
an open neighborhood, where the extension remains analytic. -/
theorem a3b4a_gysin_analytic_germ_continuous_extension
    {n c : ℕ} (ψ : (Fin n → ℂ) → (Fin c → ℂ))
    (a : Fin n → ℂ) (hψ : AnalyticAt ℂ ψ a) :
    ∃ (F : C((Fin n → ℂ), (Fin c → ℂ))) (U : Set (Fin n → ℂ)),
      IsOpen U ∧ a ∈ U ∧ (∀ z ∈ U, F z = ψ z) ∧ AnalyticOnNhd ℂ F U := by
  let V : Set (Fin n → ℂ) := {z | AnalyticAt ℂ ψ z}
  have hV : IsOpen V := isOpen_analyticAt ℂ ψ
  have hVa : a ∈ V := hψ
  have hψV : AnalyticOnNhd ℂ ψ V := fun _ hz => hz
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV a hVa
  obtain ⟨R, hRnorm, hRfix⟩ := a3b4a_gysin_exists_closedBall_retraction
    (E := Fin n → ℂ) (ε / 2) (half_pos hε).le
  let t : C((Fin n → ℂ), (Fin n → ℂ)) :=
    ⟨fun z => a + R (z - a), continuous_const.add
      (R.continuous.comp (continuous_id.sub continuous_const))⟩
  have ht (z : Fin n → ℂ) : t z ∈ V := by
    apply hεV
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖a + R (z - a) - a‖ < ε
    rw [add_sub_cancel_left]
    exact (hRnorm (z - a)).trans_lt (half_lt_self hε)
  let F : C((Fin n → ℂ), (Fin c → ℂ)) :=
    ⟨fun z => ψ (t z), hψV.continuousOn.comp_continuous t.continuous ht⟩
  have hfix : ∀ z ∈ Metric.ball a (ε / 2), F z = ψ z := by
    intro z hz
    have hz' : ‖z - a‖ ≤ ε / 2 := by
      simpa only [dist_eq_norm] using (Metric.mem_ball.mp hz).le
    change ψ (a + R (z - a)) = ψ z
    rw [hRfix (z - a) hz']
    congr 1
    abel
  refine ⟨F, Metric.ball a (ε / 2), Metric.isOpen_ball,
    Metric.mem_ball_self (half_pos hε), hfix, ?_⟩
  intro z hz
  have hzV : z ∈ V := hεV (Metric.ball_subset_ball (half_le_self hε.le) hz)
  apply (hψV z hzV).congr
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  exact (hfix w hw).symm

end HodgeLean.Adapters
