import HodgeLean.Foundations.Program.CurveJacobianFormsHol

/-!
# Track B3 foundations: periods of holomorphic forms

* `b3Forms_pathIntegral_eq`: the frozen integral `b3_pathIntegral γ θ` of a holomorphic form along
  a `C¹` path is `∫_γ Re θ + i ∫_γ Im θ`, in terms of the real line integrals of
  `CurveJacobianFormsPath.lean`;
* `b3Forms_hol_eq_zero_of_periods`: **a holomorphic form on a compact connected Riemann surface
  whose periods along all `C¹` loops vanish is zero.** If the periods vanish, `Re θ = dg` is exact
  (`b3Forms_exists_primitive`), so `∫ Re θ ∧ Im θ = ∫ d(g Im θ) = 0` by the Leibniz rule and
  Stokes' theorem, against the Riemann positivity `b3Forms_integral_reIm_pos`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

attribute [local instance] b3Forms_isManifold_real

theorem b3Forms_velocity_eq_b3 (γ : ℝ → C) (t : ℝ) :
    b3_velocity E C γ t = b3Forms_velocity (E := E) γ t := rfl

/-- **The frozen path integral of a holomorphic form**, in real and imaginary parts. -/
theorem b3Forms_pathIntegral_eq (θ : b3_HolForm E C) {γ : ℝ → C}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) :
    b3_pathIntegral E C γ θ.1 =
      (b3Forms_lineIntegral (b3Forms_reForm θ) γ 0 1 : ℂ) +
        Complex.I * (b3Forms_lineIntegral (b3Forms_imForm θ) γ 0 1 : ℂ) := by
  have hre : IntervalIntegrable (fun t ↦
      ((b3Forms_reForm θ (γ t) (fun _ ↦ b3Forms_velocity γ t) : ℝ) : ℂ)) volume 0 1 :=
    (Complex.continuous_ofReal.comp
      (b3Forms_continuous_lineIntegrand (b3Forms_isSmooth_reForm θ) hγ)).intervalIntegrable 0 1
  have him : IntervalIntegrable (fun t ↦
      ((b3Forms_imForm θ (γ t) (fun _ ↦ b3Forms_velocity γ t) : ℝ) : ℂ)) volume 0 1 :=
    (Complex.continuous_ofReal.comp
      (b3Forms_continuous_lineIntegrand (b3Forms_isSmooth_imForm θ) hγ)).intervalIntegrable 0 1
  have h : ∀ t, θ.1 ⟨γ t, b3_velocity E C γ t⟩ =
      ((b3Forms_reForm θ (γ t) (fun _ ↦ b3Forms_velocity γ t) : ℝ) : ℂ) +
        Complex.I * ((b3Forms_imForm θ (γ t) (fun _ ↦ b3Forms_velocity γ t) : ℝ) : ℂ) := by
    intro t
    rw [b3Forms_reForm_apply, b3Forms_imForm_apply, b3Forms_velocity_eq_b3]
    rw [mul_comm]
    exact (Complex.re_add_im _).symm
  simp only [b3_pathIntegral, h, b3Forms_lineIntegral]
  rw [intervalIntegral.integral_add hre (him.const_mul Complex.I),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]

theorem b3Forms_period_eq (θ : b3_HolForm E C) (γ : b3_SmoothLoop E C) :
    b3_period E C γ θ =
      (b3Forms_lineIntegral (b3Forms_reForm θ) γ.1 0 1 : ℂ) +
        Complex.I * (b3Forms_lineIntegral (b3Forms_imForm θ) γ.1 0 1 : ℂ) :=
  b3Forms_pathIntegral_eq θ γ.2.2

/-- **A holomorphic form whose real part is exact is zero** on a compact Riemann surface:
`∫ Re θ ∧ Im θ = ∫ dg ∧ Im θ = 0` against the Riemann positivity. -/
theorem b3Forms_hol_eq_zero_of_reForm_exact [T2Space C] [CompactSpace C]
    (hE : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) {g : C → ℝ}
    (hg : b3Forms_IsSmooth (b3Forms_fun (E := E) g))
    (hdg : b3Forms_d (b3Forms_fun (E := E) g) = b3Forms_reForm θ) : θ = 0 := by
  by_contra hθ
  obtain ⟨e, he, -⟩ := finrank_eq_one_iff'.1 hE
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have hpos := b3Forms_integral_reIm_pos hE he θ hθ
  have h0 := b3Forms_integral_wedge_d_eq_zero (b3Forms_cplxBasis hE he)
    (b3Forms_oriented_complex (C := C)) hg (b3Forms_isSmooth_imForm θ) (b3Forms_d_imForm hE θ)
  rw [hdg, b3Forms_pairing] at h0
  exact (ne_of_gt hpos) h0

/-- **Holomorphic forms are detected by their periods**: on a compact connected Riemann
surface, a holomorphic form whose periods along all `C¹` loops vanish is zero. -/
theorem b3Forms_hol_eq_zero_of_periods [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (θ : b3_HolForm E C)
    (h : ∀ γ : b3_SmoothLoop E C, b3_period E C γ θ = 0) : θ = 0 := by
  have hper : b3Forms_PeriodsVanish (b3Forms_reForm θ) := fun γ hp hγ ↦ by
    have h1 := congrArg Complex.re ((b3Forms_period_eq θ ⟨γ, hp, hγ⟩).symm.trans (h ⟨γ, hp, hγ⟩))
    simpa using h1
  obtain ⟨g, hg, hdg⟩ := b3Forms_exists_primitive (b3Forms_isSmooth_reForm θ)
    (b3Forms_d_reForm hE θ) hper
  exact b3Forms_hol_eq_zero_of_reForm_exact hE θ hg hdg

end HodgeLean.Foundations.Program
