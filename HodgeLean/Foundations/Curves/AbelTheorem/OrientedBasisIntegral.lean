import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open Set Manifold MeasureTheory
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℝ, E) ∞ C]
  [MeasurableSpace E] [BorelSpace E]

theorem chart_integral_eq_of_positive_basis_change {n : ℕ}
    (b b' : Module.Basis (Fin n) ℝ E) (hd : 0 < b.det b')
    (x : C) (α : C → E [⋀^Fin n]→L[ℝ] ℝ) :
    b3Forms_chartIntegral b' x α = b3Forms_chartIntegral b x α := by
  letI : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  letI : IsLocallyFiniteMeasure (ENNReal.ofReal ((b.det b')⁻¹) • b.addHaar) :=
    b.addHaar.isLocallyFiniteMeasure_smul ENNReal.ofReal_ne_top
  have hm : b'.addHaar = ENNReal.ofReal ((b.det b')⁻¹) • b.addHaar := by
    apply (Module.Basis.addHaar_eq_iff b' _).mpr
    rw [Module.Basis.coe_parallelepiped, Measure.smul_apply, MeasureTheory.Measure.addHaar_parallelepiped,
      abs_of_pos hd]
    change ENNReal.ofReal ((b.det b')⁻¹) * ENNReal.ofReal (b.det b') = 1
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hd.le), inv_mul_cancel₀ hd.ne',
      ENNReal.ofReal_one]
  have he (u : E) : b3Forms_chartFun b' x α u = (b.det b') * b3Forms_chartFun b x α u := by
    by_cases hu : u ∈ (chartAt E x).target
    · simp only [b3Forms_chartFun, Set.indicator_of_mem hu]
      have hh := congrArg (fun A : E [⋀^Fin n]→ₗ[ℝ] ℝ => A b')
        ((b3Forms_loc α x u).toAlternatingMap.eq_smul_basis_det b)
      change (b3Forms_loc α x u) b' = (b3Forms_loc α x u) b * b.det b' at hh
      exact hh.trans (mul_comm _ _)
    · simp only [b3Forms_chartFun, Set.indicator_of_notMem hu, mul_zero]
  unfold b3Forms_chartIntegral
  simp_rw [he]
  rw [hm, integral_smul_measure, integral_const_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr hd.le)]
  change (b.det b')⁻¹ * ((b.det b') * _) = _
  rw [← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul]

theorem integral_eq_of_positive_basis_change [FiniteDimensional ℝ E]
    [T2Space C] [CompactSpace C] {n : ℕ}
    (b b' : Module.Basis (Fin n) ℝ E) (hd : 0 < b.det b')
    (α : C → E [⋀^Fin n]→L[ℝ] ℝ) :
    b3Forms_integral b' α = b3Forms_integral b α := by
  simp only [b3Forms_integral, chart_integral_eq_of_positive_basis_change b b' hd]

end HodgeLean.Foundations.Curves.AbelTheorem
