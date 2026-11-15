import HodgeLean.Foundations.Program.FuchsianSystemDiscSolution
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section
open Set Metric
namespace HodgeLean.Foundations.Program

theorem b65f_regular_solution_isUnit {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {A Y : ℂ → E →L[ℂ] E} {a : ℂ} {r : ℝ}
    (hr : 0 < r) (hA : AnalyticOnNhd ℂ A (ball a r))
    (hY : ∀ z ∈ ball a r, HasDerivAt Y (A z * Y z) z)
    (hYa : Y a = 1) {z : ℂ} (hz : z ∈ ball a r) : IsUnit (Y z) := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  have hinj : Function.Injective (Y z) := by
    apply (injective_iff_map_eq_zero (Y z)).mpr
    intro v hv
    let p : ℝ → ℂ := fun t ↦ z + (t : ℂ) * (a - z)
    have hp : Continuous p := by fun_prop
    have hm : ∀ t ∈ Icc (0 : ℝ) 1, p t ∈ ball a r := by
      intro t ht
      simpa only [p, Complex.real_smul] using
        (convex_ball a r).add_smul_sub_mem hz (mem_ball_self hr) ht
    have hc : ContinuousOn (fun t ↦ A (p t)) (Icc (0 : ℝ) 1) :=
      hA.continuousOn.comp hp.continuousOn hm
    obtain ⟨M, hM, hb⟩ := (isCompact_Icc.image_of_continuousOn hc).isBounded.exists_pos_norm_le
    let f : ℝ → E := fun t ↦ Y (p t) v
    let f' : ℝ → E := fun t ↦ (a - z) • (A (p t) (f t))
    have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' t) t := by
      intro t ht
      have hdY := ((hY (p t) (hm t ht)).clm_apply (hasDerivAt_const (p t) v)).scomp t
        ((Complex.ofRealCLM.hasDerivAt.mul_const (a - z)).const_add z)
      simpa [f, f', p, Function.comp_def] using hdY
    have hf : ContinuousOn f (Icc (0 : ℝ) 1) :=
      fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt
    have hf0 : f 0 = 0 := by simpa [f, p] using hv
    have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖f' t‖ ≤ (‖a - z‖ * M) * ‖f t‖ := by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
      calc
        ‖f' t‖ = ‖a - z‖ * ‖A (p t) (f t)‖ := norm_smul _ _
        _ ≤ ‖a - z‖ * (‖A (p t)‖ * ‖f t‖) :=
          mul_le_mul_of_nonneg_left ((A (p t)).le_opNorm _) (norm_nonneg _)
        _ ≤ ‖a - z‖ * (M * ‖f t‖) := by
          gcongr
          exact hb _ (mem_image_of_mem _ ht')
        _ = _ := by ring
    have hf1 := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hf
      (fun t ht ↦ (hd t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt) hf0 hbound 1
      ⟨zero_le_one, le_rfl⟩
    simpa [f, p, hYa] using hf1
  exact ⟨hinj, (Y z).toLinearMap.injective_iff_surjective.mp hinj⟩

end HodgeLean.Foundations.Program
