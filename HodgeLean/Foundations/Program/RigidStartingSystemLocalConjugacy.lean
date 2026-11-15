import HodgeLean.Foundations.Program.FuchsianSystem

noncomputable section
open Set Metric
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65r_fuchsian_local_conjugacy (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (R : E →L[ℂ] E) (B : ℂ → E →L[ℂ] E) (a : ℂ) (d : ℝ)
    (hd : 0 < d) (hB : AnalyticOnNhd ℂ B (ball a d))
    (hnr : ∀ k : ℕ, 0 < k → Function.Bijective
      (fun T : E →L[ℂ] E ↦ (k : ℂ) • T - (R*T-T*R))) :
    ∃ r : ℝ, 0 < r ∧ r ≤ d ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r →
      ∃ C : (E →L[ℂ] E)ˣ,
        b65f_transport E (fun z ↦ (z-a)⁻¹ • R+B z) (b65f_circle a ρ) =
          (C : E →L[ℂ] E)*NormedSpace.exp ((2*Real.pi*Complex.I) • R)*↑(C⁻¹) := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  let : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
  obtain ⟨r,hr,hrd,H,hH,hH0,hu,hg,hslit,hloop⟩ :=
    b65f_local_normal_form E R B a d hd hB hnr
  refine ⟨r,hr,hrd,?_⟩
  intro ρ hρ hρr
  let Q := fun t : ℝ ↦ H (b65f_circle a ρ t)*
    NormedSpace.exp ((Complex.log (ρ : ℂ)+2*Real.pi*Complex.I*(t : ℂ)) • R)
  obtain ⟨hQ,hend,htrans⟩ := hloop ρ hρ hρr
  have hc : b65f_circle a ρ 0 ∈ ball a r := by
    rw [mem_ball_iff_norm, b65f_circle_norm, abs_of_pos hρ]
    exact hρr
  have hunit : IsUnit (Q 0) :=
    (hu _ hc).mul (NormedSpace.isUnit_exp _)
  let C := hunit.unit
  have hC : C.val = Q 0 := hunit.unit_spec
  have he : b65f_transport E (fun z ↦ (z-a)⁻¹ • R+B z) (b65f_circle a ρ)*C.val =
      C.val*NormedSpace.exp ((2*Real.pi*Complex.I) • R) := by
    rw [hC]
    exact htrans.trans hend
  refine ⟨C,?_⟩
  calc
    _ = (b65f_transport E (fun z ↦ (z-a)⁻¹ • R+B z) (b65f_circle a ρ)*C.val)*(C⁻¹).val := by
      simp [mul_assoc]
    _ = _ := by rw [he]

theorem b65r_conjugator_of_intertwining {A : Type*} [Monoid A]
    (M E X : A) (hu : IsUnit X) (h : M*X = X*E) :
    ∃ C : Aˣ, M = C*E*↑(C⁻¹) := by
  let C := hu.unit
  have hc : C.val = X := hu.unit_spec
  refine ⟨C,?_⟩
  calc
    M = (M*X)*(C⁻¹).val := by rw [← hc]; simp [mul_assoc]
    _ = (X*E)*(C⁻¹).val := by rw [h]
    _ = _ := by rw [hc]

theorem b65r_gauge_local_conjugacy (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (R : E →L[ℂ] E) (A H : ℂ → E →L[ℂ] E) (a : ℂ) (r : ℝ)
    (hA : AnalyticOnNhd ℂ A (ball a r \ {a}))
    (hH : AnalyticOnNhd ℂ H (ball a r))
    (hu : ∀ z ∈ ball a r, IsUnit (H z))
    (hg : ∀ z ∈ ball a r \ {a}, (z-a) • deriv H z = (z-a) • (A z*H z)-H z*R)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ < r) :
    ∃ C : (E →L[ℂ] E)ˣ,
      b65f_transport E A (b65f_circle a ρ) =
        (C : E →L[ℂ] E)*NormedSpace.exp ((2*Real.pi*Complex.I) • R)*↑(C⁻¹) := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  let : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
  let U : Set ℂ := ball a r \ {a}
  let B := fun z ↦ A z-(z-a)⁻¹ • R
  let Q := fun t : ℝ ↦ H (b65f_circle a ρ t)*
    NormedSpace.exp ((Complex.log (ρ : ℂ)+2*Real.pi*Complex.I*(t : ℂ)) • R)
  have hform (z : ℂ) : (z-a)⁻¹ • R+B z = A z := by dsimp [B]; abel
  have hcircle (t : ℝ) : b65f_circle a ρ t ∈ ball a r := by
    rw [mem_ball_iff_norm, b65f_circle_norm, abs_of_pos hρ]
    exact hρr
  have hne (t : ℝ) : b65f_circle a ρ t-a ≠ 0 := by
    apply norm_pos_iff.mp
    rw [b65f_circle_norm, abs_of_pos hρ]
    exact hρ
  have hm (t : ℝ) : b65f_circle a ρ t ∈ U :=
    ⟨hcircle t, by simpa only [mem_singleton_iff] using sub_ne_zero.mp (hne t)⟩
  have hQ (t : ℝ) : HasDerivAt Q
      ((2*Real.pi*Complex.I*(b65f_circle a ρ t-a)) • (A (b65f_circle a ρ t)*Q t)) t := by
    have hgc : (b65f_circle a ρ t-a) • deriv H (b65f_circle a ρ t) =
        R*H (b65f_circle a ρ t)-H (b65f_circle a ρ t)*R+
          (b65f_circle a ρ t-a) • (B (b65f_circle a ρ t)*H (b65f_circle a ρ t)) := by
      rw [hg _ (hm t)]
      dsimp only [B]
      simp only [sub_mul, smul_sub, smul_mul_assoc, smul_smul,
        mul_inv_cancel₀ (hne t), one_smul]
      abel
    simpa only [hform] using b65f_lifted_circle_hasDerivAt R B H a ρ t hρ
      (hH _ (hcircle t)).differentiableAt hgc
  have htrans : b65f_transport E A (b65f_circle a ρ)*Q 0 = Q 1 :=
    b65f_smooth_transport_propagates (isOpen_ball.sdiff isClosed_singleton) hA
      (b65f_circle a ρ) (fun t ↦ 2*Real.pi*Complex.I*(b65f_circle a ρ t-a)) Q
      (by unfold b65f_circle; fun_prop) (by unfold b65f_circle; fun_prop) (fun t _ ↦ hm t)
      (fun t _ ↦ b65f_circle_hasDerivAt a ρ t) (fun t _ ↦ hQ t)
  have hend : Q 1 = Q 0*NormedSpace.exp ((2*Real.pi*Complex.I) • R) :=
    b65f_lifted_circle_endpoint R H a ρ
  exact b65r_conjugator_of_intertwining _ _ (Q 0)
    ((hu _ (hcircle 0)).mul (NormedSpace.isUnit_exp _)) (htrans.trans hend)

end HodgeLean.Foundations.Program
