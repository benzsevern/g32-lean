import HodgeLean.Foundations.Program.FuchsianSystemUnits

noncomputable section
open Set Metric
namespace HodgeLean.Foundations.Program

theorem b65f_regular_solution_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : ℂ → E →L[ℂ] E} {f g : ℂ → E} {a : ℂ} {r : ℝ}
    (hr : 0 < r) (hA : AnalyticOnNhd ℂ A (ball a r))
    (hf : ∀ z ∈ ball a r, HasDerivAt f (A z (f z)) z)
    (hg : ∀ z ∈ ball a r, HasDerivAt g (A z (g z)) z)
    (hfg : f a = g a) : EqOn f g (ball a r) := by
  intro z hz
  let p : ℝ → ℂ := fun t ↦ a + (t : ℂ) * (z - a)
  have hp : Continuous p := by fun_prop
  have hm : ∀ t ∈ Icc (0 : ℝ) 1, p t ∈ ball a r := by
    intro t ht
    exact b65f_segment_mem_ball hz ht
  have hc : ContinuousOn (fun t ↦ A (p t)) (Icc (0 : ℝ) 1) :=
    hA.continuousOn.comp hp.continuousOn hm
  obtain ⟨M, hM, hb⟩ := (isCompact_Icc.image_of_continuousOn hc).isBounded.exists_pos_norm_le
  let h : ℝ → E := fun t ↦ f (p t) - g (p t)
  let h' : ℝ → E := fun t ↦ (z - a) • (A (p t) (h t))
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt h (h' t) t := by
    intro t ht
    have hsub := ((hf _ (hm t ht)).sub (hg _ (hm t ht))).scomp t
      ((Complex.ofRealCLM.hasDerivAt.mul_const (z - a)).const_add a)
    simpa [h, h', p, Function.comp_def, map_sub] using hsub
  have hh : ContinuousOn h (Icc (0 : ℝ) 1) :=
    fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt
  have hh0 : h 0 = 0 := by simp [h, p, hfg]
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖h' t‖ ≤ (‖z - a‖ * M) * ‖h t‖ := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    calc
      ‖h' t‖ = ‖z - a‖ * ‖A (p t) (h t)‖ := norm_smul _ _
      _ ≤ ‖z - a‖ * (‖A (p t)‖ * ‖h t‖) :=
        mul_le_mul_of_nonneg_left ((A (p t)).le_opNorm _) (norm_nonneg _)
      _ ≤ ‖z - a‖ * (M * ‖h t‖) := by
        gcongr
        exact hb _ (mem_image_of_mem _ ht')
      _ = _ := by ring
  have hh1 := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hh
    (fun t ht ↦ (hd t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt) hh0 hbound 1
    ⟨zero_le_one, le_rfl⟩
  exact sub_eq_zero.mp (by simpa [h, p] using hh1)

theorem b65f_segment_propagates {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {A Y : ℂ → E →L[ℂ] E} {u v : ℂ} {r : ℝ}
    (hr : 0 < r) (hA : AnalyticOnNhd ℂ A (ball u r))
    (hY : ∀ z ∈ ball u r, HasDerivAt Y (A z * Y z) z)
    (hv : v ∈ ball u r) : b65f_segment E A u v * Y u = Y v := by
  have hd : ∀ z ∈ ball u r, HasDerivAt (fun w ↦ b65f_segment E A u w * Y u)
      (A z * (b65f_segment E A u z * Y u)) z := by
    intro z hz
    simpa only [mul_assoc] using (b65f_segment_hasDerivAt hA hz).mul_const (Y u)
  exact b65f_regular_solution_unique hr (b65f_leftCoefficient_analytic hA)
    hd hY (by rw [b65f_segment_initial, one_mul]) hv

end HodgeLean.Foundations.Program
