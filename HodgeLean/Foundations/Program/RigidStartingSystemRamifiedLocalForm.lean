import HodgeLean.Foundations.Program.RigidStartingSystemRamifiedGauge
import HodgeLean.Foundations.Program.RigidStartingSystemLocalLog
import HodgeLean.Foundations.Program.RigidStartingSystemRamificationScalar
import HodgeLean.Foundations.Program.RigidStartingSystemLocalConjugacy

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65r_ramified_local_gauge (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (R : E →L[ℂ] E) (B : ℂ → E →L[ℂ] E) (d : ℝ) (hd : 0 < d)
    (hB : AnalyticOnNhd ℂ B (ball 0 d))
    (hnr : ∀ k : ℕ, 0 < k → Function.Bijective
      (fun T : E →L[ℂ] E ↦ (k : ℂ) • T-(R*T-T*R)))
    (φ g : ℂ → ℂ) (a : ℂ) (e : ℕ) (he : 0 < e)
    (hφ : AnalyticAt ℂ φ a) (hg : AnalyticAt ℂ g a) (hga : g a ≠ 0)
    (hfactor : ∀ z, φ z = (z-a)^e*g z) :
    ∃ r : ℝ, 0 < r ∧ ∃ K : ℂ → E →L[ℂ] E,
      AnalyticOnNhd ℂ (fun z ↦ deriv φ z • ((φ z)⁻¹ • R+B (φ z))) (ball a r \ {a}) ∧
      AnalyticOnNhd ℂ K (ball a r) ∧ (∀ z ∈ ball a r, IsUnit (K z)) ∧
      ∀ z ∈ ball a r \ {a}, (z-a) • deriv K z =
        (z-a) • ((deriv φ z • ((φ z)⁻¹ • R+B (φ z)))*K z)-K z*((e : ℂ) • R) := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨rH,hrH,hrHd,H,hH,hH0,hu,hbase,hslit,hloop⟩ :=
    b65f_local_normal_form E R B 0 d hd hB hnr
  obtain ⟨rφ,hrφ,hφ0⟩ := hφ.exists_ball_analyticOnNhd
  obtain ⟨rL,hrL,hg0,hsl,hL0⟩ := b65r_localLog_neighbourhood g a hg hga
  have hφa : φ a = 0 := by rw [hfactor, sub_self, zero_pow (Nat.ne_of_gt he), zero_mul]
  have hmap : ∀ᶠ z in 𝓝 a, φ z ∈ ball 0 rH :=
    hφ.continuousAt.tendsto.eventually (isOpen_ball.mem_nhds (by
      rw [hφa]; exact mem_ball_self hrH))
  obtain ⟨rM,hrM,hM⟩ := Metric.mem_nhds_iff.mp hmap
  let r := min rφ (min rL rM)
  let L := b65r_localLog g a
  let K := b65r_ramifiedGauge R H φ L
  have hpφ : ball a r ⊆ ball a rφ := ball_subset_ball (min_le_left _ _)
  have hpL : ball a r ⊆ ball a rL :=
    ball_subset_ball (le_trans (min_le_right _ _) (min_le_left _ _))
  have hpM : ball a r ⊆ ball a rM :=
    ball_subset_ball (le_trans (min_le_right _ _) (min_le_right _ _))
  have hgne (z : ℂ) (hz : z ∈ ball a r) : g z ≠ 0 := by
    have hs := hsl z (hpL hz)
    intro h
    rw [h, zero_div] at hs
    exact Complex.slitPlane_ne_zero hs rfl
  have hφne (z : ℂ) (hz : z ∈ ball a r \ {a}) : φ z ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (by simpa using hz.2))) (hgne z hz.1)
  refine ⟨r,lt_min hrφ (lt_min hrL hrM),K,?_,?_,?_,?_⟩
  · intro z hz
    have haφ := hφ0 z (hpφ hz.1)
    have hb := hB (φ z) (ball_subset_ball hrHd (hM (hpM hz.1)))
    exact haφ.deriv.smul (((haφ.inv (hφne z hz)).smul analyticAt_const).add (hb.comp (f := φ) haφ))
  · intro z hz
    exact b65r_ramifiedGauge_analyticAt R H φ L z (hH _ (hM (hpM hz)))
      (hφ0 z (hpφ hz)) (hL0 z (hpL hz))
  · intro z hz
    exact b65r_ramifiedGauge_isUnit R H φ L z (hu _ (hM (hpM hz)))
  · intro z hz
    have hza : z ≠ a := by simpa using hz.2
    have hφD := (hφ0 z (hpφ hz.1)).differentiableAt.hasDerivAt
    have hgD := (hg0 z (hpL hz.1)).differentiableAt.hasDerivAt
    have hLD := b65r_localLog_hasDerivAt g a z (deriv g z) hgD hga (hsl z (hpL hz.1))
    have hlog := b65r_logDerivative_power_factor φ g a z (deriv φ z) (deriv g z)
      e he hza (hgne z hz.1) hfactor hφD hgD
    have hy := hM (hpM hz.1)
    have hD : deriv H (φ z) = ((φ z)⁻¹ • R+B (φ z))*H (φ z)-H (φ z)*((φ z)⁻¹ • R) := by
      rw [b65f_gauge_derivative_rescale R B H 0 (φ z) (by simpa using hφne z hz) (hbase _ hy)]
      simp only [sub_zero, smul_sub, add_mul, smul_mul_assoc, mul_smul_comm]
      abel
    have hHD : HasDerivAt H
        (((φ z)⁻¹ • R+B (φ z))*H (φ z)-H (φ z)*((φ z)⁻¹ • R)) (φ z) := by
      rw [← hD]
      exact (hH _ hy).differentiableAt.hasDerivAt
    exact b65r_ramifiedGauge_equation R (fun y ↦ y⁻¹ • R+B y) H φ L
      z (deriv φ z) (deriv g z/g z) (e : ℂ) a hza hφD hLD hHD hlog

end HodgeLean.Foundations.Program
