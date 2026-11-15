import HodgeLean.Foundations.Curves.AbelTheorem.MeromorphicDualLinearity
import HodgeLean.Foundations.Curves.AbelTheorem.WeightedResidueStokes
import HodgeLean.Foundations.Curves.AbelTheorem.ResiduePoleSupport
import HodgeLean.Foundations.Curves.AbelTheorem.SmoothScalarFromForm
import HodgeLean.Foundations.Curves.AbelTheorem.LocalConstantPrimitive

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold MeasureTheory
open scoped Topology ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C]
  [MeasurableSpace E] [BorelSpace E]
attribute [local instance] b3Forms_isManifold_real

theorem meromorphic_period_relation_of_dual_primitive (h : Module.finrank ℂ E = 1)
    (D : C →₀ ℤ) (w : b4c_MeroForm E C h)
    (hr : ∀ x, b4c_res (hE := h) w x = (D x : ℂ))
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0)
    {ι : Type} [Fintype ι] (η : ι → C → E [⋀^Fin 1]→L[ℝ] ℝ)
    (hη : ∀ i, b3Forms_IsSmooth (η i))
    (hzero : ∀ i x, x ∈ D.support → η i =ᶠ[𝓝 x] 0)
    (n : ι → ℤ) (f : C → ℝ)
    (hf : b3Forms_IsSmooth (b3Forms_fun (E := E) f))
    (hdf : b3Forms_d (b3Forms_fun (E := E) f) = ∑ i, (n i : ℝ) • η i)
    (v : ι → ℂ)
    (hpair : ∀ (P : ℂ →L[ℝ] ℝ) i, b3Forms_integral (b4c_residue_basis h)
      (b3Forms_wedgeForm (b4c_residue_realForm h (b4c_residue_normalizedForm h w) P) (η i)) =
        P (v i)) (N : ℤ) (hN : ∑ x ∈ D.support, (D x : ℝ) * f x = (N : ℝ)) :
    ∑ i, (n i : ℂ) * v i = (2 * Real.pi * Complex.I) * (N : ℂ) := by
  classical
  have hpoles := pole_set_eq_residue_divisor_support h D w hr ha
  have hc : ∀ x, meromorphicOrderAt (HurwitzPrymRR_loc h w x) 0 < 0 →
      f =ᶠ[𝓝 x] fun _ => f x := by
    intro x hx
    have hxs : x ∈ D.support := hpoles ▸ (b4c_residue_poles_finite h w).mem_toFinset.mpr hx
    apply constant_germ_of_differential_zero_near f hf x
    rw [hdf]
    have he : ∀ᶠ y in 𝓝 x, ∀ i, η i y = 0 := by
      rw [Filter.eventually_all]
      intro i
      filter_upwards [hzero i x hxs] with y hy
      exact hy
    filter_upwards [he] with y hy
    simp only [Finset.sum_apply, Pi.smul_apply, hy, smul_zero, Finset.sum_const_zero,
      Pi.zero_apply]
  have he (P : ℂ →L[ℝ] ℝ) : P (∑ i, (n i : ℂ) * v i) =
      P ((2 * Real.pi * Complex.I) * (N : ℂ)) := by
    have hw := weighted_residue_stokes_of_constant_germs h w f
      (smooth_scalar_of_smooth_zero_form f hf) hc P
    rw [meromorphic_dual_primitive_pairing h D w ha η hη hzero n f hdf v P (hpair P),
      hpoles] at hw
    have hcast (k : ℤ) : P ((2 * Real.pi * Complex.I) * (k : ℂ)) =
        (k : ℝ) * P (2 * Real.pi * Complex.I) := by
      rw [mul_comm]
      simp only [← zsmul_eq_mul, map_zsmul]
    have hs : ∑ x ∈ D.support, f x * P (2 * (Real.pi : ℂ) * Complex.I * b4c_res (hE := h) w x) =
        P ((2 * Real.pi * Complex.I) * (N : ℂ)) := by
      simp only [hr, hcast]
      rw [← hN, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hs] at hw
    exact neg_inj.mp hw
  exact Complex.ext (he Complex.reCLM) (he Complex.imCLM)

end HodgeLean.Foundations.Curves.AbelTheorem
