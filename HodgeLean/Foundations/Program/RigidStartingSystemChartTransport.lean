import HodgeLean.Foundations.Program.RigidStartingSystemLocalConjugacy

noncomputable section
open Set Metric
namespace HodgeLean.Foundations.Program

theorem b65r_chart_lift_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E]
    (R : E →L[ℂ] E) (B H : ℂ → E →L[ℂ] E) (w : ℝ → ℂ)
    (t : ℝ) (hw : HasDerivAt w (2*Real.pi*Complex.I*w t) t)
    (hH : DifferentiableAt ℂ H (w t))
    (hg : w t • deriv H (w t) = w t • (B (w t)*H (w t))-H (w t)*R) :
    HasDerivAt (fun s : ℝ ↦ H (w s)*
      NormedSpace.exp ((2*Real.pi*Complex.I*(s : ℂ)) • R))
      ((2*Real.pi*Complex.I*w t) • (B (w t)*(H (w t)*
        NormedSpace.exp ((2*Real.pi*Complex.I*(t : ℂ)) • R)))) t := by
  let c : ℂ := 2*Real.pi*Complex.I
  have he := (hasDerivAt_exp_smul_const' R (c*(t : ℂ))).scomp t
    (Complex.ofRealCLM.hasDerivAt.const_mul c)
  have hh := (hH.hasDerivAt.scomp t hw).mul he
  convert hh using 1
  · rfl
  · simp only [Function.comp_apply,Complex.ofRealCLM_apply,Complex.ofReal_one,mul_one]
    have hc := congrArg (fun X : E →L[ℂ] E ↦ c • X) hg
    simp only [smul_sub,smul_smul] at hc
    rw [hc]
    dsimp only [c]
    simp only [sub_mul,smul_mul_assoc,mul_smul_comm,smul_smul,mul_assoc]
    abel

theorem b65r_chart_loop_conjugacy (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (U : Set ℂ) (hU : IsOpen U) (A : ℂ → E →L[ℂ] E) (hA : AnalyticOnNhd ℂ A U)
    (R : E →L[ℂ] E) (B H : ℂ → E →L[ℂ] E) (r : ℝ)
    (hH : AnalyticOnNhd ℂ H (ball 0 r)) (hu : ∀ z ∈ ball 0 r, IsUnit (H z))
    (hg : ∀ z ∈ ball 0 r, z ≠ 0 → z • deriv H z = z • (B z*H z)-H z*R)
    (γ w : ℝ → ℂ) (v : ℝ → ℂ)
    (hγ : Continuous γ) (hv : Continuous v) (hm : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt γ (v t) t)
    (hw : ∀ t, w t ∈ ball 0 r ∧ w t ≠ 0)
    (hwd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt w (2*Real.pi*Complex.I*w t) t)
    (hperiod : w 1 = w 0)
    (hrel : ∀ t ∈ Icc (0 : ℝ) 1,
      v t • A (γ t) = (2*Real.pi*Complex.I*w t) • B (w t)) :
    ∃ C : (E →L[ℂ] E)ˣ,
      b65f_transport E A γ = C.val*NormedSpace.exp ((2*Real.pi*Complex.I) • R)*(C⁻¹).val := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  let : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
  let Q := fun t : ℝ ↦ H (w t)*NormedSpace.exp ((2*Real.pi*Complex.I*(t : ℂ)) • R)
  have hQ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt Q (v t • (A (γ t)*Q t)) t := by
    have h := b65r_chart_lift_derivative R B H w t (hwd t ht)
      (hH _ (hw t).1).differentiableAt (hg _ (hw t).1 (hw t).2)
    simpa only [← smul_mul_assoc,← hrel t ht] using h
  have ht := b65f_smooth_transport_propagates hU hA γ v Q hγ.continuousOn hv.continuousOn hm hd hQ
  have he : Q 1 = Q 0*NormedSpace.exp ((2*Real.pi*Complex.I) • R) := by
    simp [Q,hperiod]
  have hunit : IsUnit (Q 0) := by simpa [Q] using hu _ (hw 0).1
  exact b65r_conjugator_of_intertwining _ _ _ hunit (ht.trans he)

end HodgeLean.Foundations.Program
