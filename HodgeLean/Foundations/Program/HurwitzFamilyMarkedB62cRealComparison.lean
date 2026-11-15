import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cRadial

noncomputable section

namespace HodgeLean.Foundations.Program

open scoped Topology

theorem b6m_differentiableAt_real_of_analytic_comp {g k : ℂ → ℂ} {z : ℂ}
    (hg : ContinuousAt g z) (hk : AnalyticAt ℂ k (g z))
    (hkd : fderiv ℂ k (g z) ≠ 0) (hkg : DifferentiableAt ℝ (k ∘ g) z) :
    DifferentiableAt ℝ g z := by
  obtain ⟨s, hs, _, _, hsk⟩ := b4cov_exists_localInverse (by simp) (by simp) hk hkd
  have heq : g =ᶠ[𝓝 z] s ∘ (k ∘ g) := by
    filter_upwards [hg.eventually hsk] with w hw
    exact hw.symm
  exact (((hs.differentiableAt.restrictScalars ℝ).comp z hkg)).congr_of_eventuallyEq heq

theorem b6m_complexLinear_injective_of_ne_zero (L : ℂ →L[ℂ] ℂ) (hL : L ≠ 0) :
    Function.Injective L := by
  have hm : ∀ z : ℂ, L z = z * L 1 := fun z ↦ by
    simpa only [smul_eq_mul, mul_one] using L.map_smul z 1
  have h1 : L 1 ≠ 0 := by
    intro h
    apply hL
    apply ContinuousLinearMap.ext
    intro z
    change L z = 0
    rw [hm, h, mul_zero]
  intro x y hxy
  rw [hm x, hm y] at hxy
  exact mul_right_cancel₀ h1 hxy

theorem b6m_analytic_real_derivative_orientation {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hfd : fderiv ℂ f z ≠ 0) (v w : ℂ) :
    SignType.sign (b3_orient ℂ (fderiv ℝ f z v) (fderiv ℝ f z w)) =
      SignType.sign (b3_orient ℂ v w) := by
  rw [hf.differentiableAt.fderiv_restrictScalars ℝ]
  exact b6m_orient_sign_complexLinear (fderiv ℂ f z)
    (b6m_complexLinear_injective_of_ne_zero _ hfd) v w

theorem b6m_real_comparison_orientation {f k g h : ℂ → ℂ} {z : ℂ}
    (hg : ContinuousAt g z) (hf : AnalyticAt ℂ f z) (hk : AnalyticAt ℂ k (g z))
    (hfd : fderiv ℂ f z ≠ 0) (hkd : fderiv ℂ k (g z) ≠ 0)
    (hh : DifferentiableAt ℝ h (f z))
    (ho : ∀ v w : ℂ, SignType.sign (b3_orient ℂ
      (fderiv ℝ h (f z) v) (fderiv ℝ h (f z) w)) = SignType.sign (b3_orient ℂ v w))
    (he : k ∘ g =ᶠ[𝓝 z] h ∘ f) :
    DifferentiableAt ℝ g z ∧ ∀ v w : ℂ,
      SignType.sign (b3_orient ℂ (fderiv ℝ g z v) (fderiv ℝ g z w)) =
        SignType.sign (b3_orient ℂ v w) := by
  have hfR := hf.differentiableAt.restrictScalars ℝ
  have hkR := hk.differentiableAt.restrictScalars ℝ
  have hkg : DifferentiableAt ℝ (k ∘ g) z :=
    (hh.comp z hfR).congr_of_eventuallyEq he
  have hgR := b6m_differentiableAt_real_of_analytic_comp hg hk hkd hkg
  have hc : ∀ v : ℂ, fderiv ℝ k (g z) (fderiv ℝ g z v) =
      fderiv ℝ h (f z) (fderiv ℝ f z v) := by
    have H := he.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_comp z hkR hgR, fderiv_comp z hh hfR] at H
    exact fun v ↦ congrArg (fun L : ℂ →L[ℝ] ℂ ↦ L v) H
  refine ⟨hgR, fun v w ↦ ?_⟩
  calc
    SignType.sign (b3_orient ℂ (fderiv ℝ g z v) (fderiv ℝ g z w)) =
        SignType.sign (b3_orient ℂ
          (fderiv ℝ k (g z) (fderiv ℝ g z v))
          (fderiv ℝ k (g z) (fderiv ℝ g z w))) :=
      (b6m_analytic_real_derivative_orientation hk hkd _ _).symm
    _ = SignType.sign (b3_orient ℂ
        (fderiv ℝ h (f z) (fderiv ℝ f z v))
        (fderiv ℝ h (f z) (fderiv ℝ f z w))) := by rw [hc v, hc w]
    _ = SignType.sign (b3_orient ℂ (fderiv ℝ f z v) (fderiv ℝ f z w)) := ho _ _
    _ = SignType.sign (b3_orient ℂ v w) := b6m_analytic_real_derivative_orientation hf hfd v w

end HodgeLean.Foundations.Program
