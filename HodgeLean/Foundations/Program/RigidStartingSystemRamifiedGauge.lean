import HodgeLean.Foundations.Program.FuchsianSystemCircle

noncomputable section
namespace HodgeLean.Foundations.Program

def b65r_ramifiedGauge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : E →L[ℂ] E) (H : ℂ → E →L[ℂ] E) (φ L : ℂ → ℂ) (z : ℂ) : E →L[ℂ] E :=
  H (φ z)*NormedSpace.exp (L z • R)

theorem b65r_ramifiedGauge_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (R : E →L[ℂ] E) (A H : ℂ → E →L[ℂ] E) (φ L : ℂ → ℂ)
    (z φ' L' e a : ℂ)
    (hφ : HasDerivAt φ φ' z) (hL : HasDerivAt L L' z)
    (hH : HasDerivAt H (A (φ z)*H (φ z)-H (φ z)*((φ z)⁻¹ • R)) (φ z))
    (hlog : φ'/φ z-L' = e/(z-a)) :
    HasDerivAt (b65r_ramifiedGauge R H φ L)
      (φ' • (A (φ z)*b65r_ramifiedGauge R H φ L z)-
        (e/(z-a)) • (b65r_ramifiedGauge R H φ L z*R)) z := by
  let : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
  have he := (hasDerivAt_exp_smul_const' R (L z)).scomp z hL
  have hh := (hH.scomp z hφ).mul he
  have hc : R*NormedSpace.exp (L z • R) = NormedSpace.exp (L z • R)*R :=
    SemiconjBy.exp_right ((Commute.refl R).smul_right (L z))
  convert hh using 1
  · rfl
  · dsimp only [b65r_ramifiedGauge, Function.comp_apply]
    simp only [smul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
    rw [hc, ← hlog]
    simp only [div_eq_mul_inv, sub_smul]
    abel

theorem b65r_ramifiedGauge_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (R : E →L[ℂ] E) (H : ℂ → E →L[ℂ] E) (φ L : ℂ → ℂ) (z : ℂ)
    (hH : AnalyticAt ℂ H (φ z)) (hφ : AnalyticAt ℂ φ z) (hL : AnalyticAt ℂ L z) :
    AnalyticAt ℂ (b65r_ramifiedGauge R H φ L) z := by
  have he : AnalyticAt ℂ NormedSpace.exp (L z • R) :=
    NormedSpace.analyticAt_exp_of_mem_ball _
      ((NormedSpace.expSeries_radius_eq_top ℂ (E →L[ℂ] E)).symm ▸ edist_lt_top _ _)
  have hs : AnalyticAt ℂ (fun w : ℂ ↦ L w • R) z := hL.smul analyticAt_const
  exact (hH.comp (f := φ) hφ).mul (he.comp (f := fun w : ℂ ↦ L w • R) hs)

theorem b65r_ramifiedGauge_isUnit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (R : E →L[ℂ] E) (H : ℂ → E →L[ℂ] E) (φ L : ℂ → ℂ) (z : ℂ)
    (hH : IsUnit (H (φ z))) : IsUnit (b65r_ramifiedGauge R H φ L z) := by
  let : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact hH.mul (NormedSpace.isUnit_exp _)

theorem b65r_ramifiedGauge_equation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (R : E →L[ℂ] E) (A H : ℂ → E →L[ℂ] E) (φ L : ℂ → ℂ)
    (z φ' L' e a : ℂ) (hz : z ≠ a)
    (hφ : HasDerivAt φ φ' z) (hL : HasDerivAt L L' z)
    (hH : HasDerivAt H (A (φ z)*H (φ z)-H (φ z)*((φ z)⁻¹ • R)) (φ z))
    (hlog : φ'/φ z-L' = e/(z-a)) :
    (z-a) • deriv (b65r_ramifiedGauge R H φ L) z =
      (z-a) • ((φ' • A (φ z))*b65r_ramifiedGauge R H φ L z)-
        b65r_ramifiedGauge R H φ L z*(e • R) := by
  rw [(b65r_ramifiedGauge_hasDerivAt R A H φ L z φ' L' e a hφ hL hH hlog).deriv]
  have hw : z-a ≠ 0 := sub_ne_zero.mpr hz
  have he : (z-a)*(e/(z-a)) = e := by field_simp
  simp only [smul_sub, smul_smul, smul_mul_assoc, mul_smul_comm, he]

end HodgeLean.Foundations.Program
