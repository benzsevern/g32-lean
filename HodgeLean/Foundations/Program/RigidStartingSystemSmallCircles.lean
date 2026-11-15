import HodgeLean.Foundations.Program.RigidStartingSystemSourceCharts
import HodgeLean.Foundations.Program.RigidStartingSystemChartTransport
import HodgeLean.Foundations.Program.RigidStartingSystemMonodromyClasses
import HodgeLean.Foundations.Program.RigidStartingSystemNonresonance

noncomputable section
open Set Metric
namespace HodgeLean.Foundations.Program

theorem b65r_small_source_circles (i : Fin 4) :
    ∃ s : ℝ, 0 < s ∧ ∀ w : ℂ, w ≠ 0 → ‖w‖ < s →
      ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
        b65f_transport (Fin 4 → ℂ) b65r_A
          (fun t ↦ b65r_sourceChart i (Complex.exp (2*Real.pi*Complex.I*(t : ℂ))*w)) =
          C.val*b65r_operator (b4b_toMatrix (b4b_generators i))*(C⁻¹).val := by
  obtain ⟨d,hd,hB⟩ := (b65r_regularPart_analyticAt i).exists_ball_analyticOnNhd
  obtain ⟨r,hr,hrd,H,hH,hH0,hu,hg,-,-⟩ := b65f_local_normal_form (Fin 4 → ℂ)
    (b65r_operator (b65r_residues i)) (b65r_regularPart i) 0 d hd hB
    (b65r_residues_nonresonance i)
  refine ⟨min r (1/8),lt_min hr (by norm_num),fun w hw0 hw ↦ ?_⟩
  let c : ℂ := 2*Real.pi*Complex.I
  let z : ℝ → ℂ := fun t ↦ Complex.exp (c*(t : ℂ))*w
  have hzn (t : ℝ) : ‖z t‖ = ‖w‖ := by
    simp [z,c,norm_mul,Complex.norm_exp,Complex.mul_re,Complex.mul_im]
  have hz0 (t : ℝ) : z t ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) hw0
  have hzr (t : ℝ) : z t ∈ ball 0 r := by
    rw [mem_ball_zero_iff,hzn]
    exact hw.trans_le (min_le_left _ _)
  have hzs (t : ℝ) : ‖z t‖ < 1/8 := (hzn t) ▸ hw.trans_le (min_le_right _ _)
  have hzm (t : ℝ) : b65r_sourceChart i (z t) ∈ b65r_sourceDomain :=
    b65r_sourceChart_avoids i (z t) (hz0 t) (hzs t)
  have hzd (t : ℝ) : HasDerivAt z (c*z t) t := by
    convert ((Complex.hasDerivAt_exp (c*(t : ℂ))).scomp t
      (Complex.ofRealCLM.hasDerivAt.const_mul c)).mul_const w using 1
    · rfl
    · simp only [Complex.ofRealCLM_apply,Complex.ofReal_one,mul_one]; dsimp [z]; ring
  have hgd (t : ℝ) : HasDerivAt (fun t ↦ b65r_sourceChart i (z t))
      (deriv (b65r_sourceChart i) (z t)*(c*z t)) t :=
    by
      convert ((b65r_sourceChart_analytic i (z t) (hz0 t)).differentiableAt.hasDerivAt).scomp t (hzd t) using 1
      · rfl
      · change deriv (b65r_sourceChart i) (z t)*(c*z t) =
          (c*z t)*deriv (b65r_sourceChart i) (z t)
        ring
  have hG : ∀ u ∈ ball 0 r, u ≠ 0 →
      u • deriv H u = u • (b65r_sourceCoefficient i u*H u)-H u*b65r_operator (b65r_residues i) := by
    intro u hum hu0
    have hh := hg u hum
    simp only [sub_zero] at hh
    rw [hh]
    dsimp [b65r_sourceCoefficient]
    simp only [add_mul,smul_add,smul_mul_assoc,smul_smul,mul_inv_cancel₀ hu0,one_smul]
    abel
  obtain ⟨C,hC⟩ := b65r_chart_loop_conjugacy (Fin 4 → ℂ) b65r_sourceDomain
    b65r_sourceDomain_open b65r_A b65r_A_analytic (b65r_operator (b65r_residues i))
    (b65r_sourceCoefficient i) H r hH hu hG
    (fun t ↦ b65r_sourceChart i (z t)) z
    (fun t ↦ deriv (b65r_sourceChart i) (z t)*(c*z t))
    (by
      have hzcont : Continuous z := by dsimp [z]; fun_prop
      exact continuous_iff_continuousAt.mpr (fun t ↦
        ((b65r_sourceChart_analytic i (z t) (hz0 t)).continuousAt).comp hzcont.continuousAt))
    (by
      have hzcont : Continuous z := by dsimp [z]; fun_prop
      have hder : Continuous (fun t ↦ deriv (b65r_sourceChart i) (z t)) := by
        apply continuous_iff_continuousAt.mpr
        intro t
        exact ((b65r_sourceChart_analytic i (z t) (hz0 t)).deriv.continuousAt).comp
          (hzcont.continuousAt)
      exact hder.mul (continuous_const.mul hzcont))
    (fun t _ ↦ hzm t) (fun t _ ↦ hgd t) (fun t ↦ ⟨hzr t,hz0 t⟩)
    (fun t _ ↦ hzd t) (by simp [z,c,Complex.exp_two_pi_mul_I])
    (by
      intro t ht
      rw [mul_comm (deriv (b65r_sourceChart i) (z t)),mul_smul,
        b65r_sourceChart_relation i (z t) (hz0 t) (hzm t)])
  obtain ⟨D,hD⟩ := b65r_residue_exponential_class i
  exact b65r_change_local_class _ _ _ C D hC hD

end HodgeLean.Foundations.Program
