import HodgeLean.Foundations.Curves.AbelTheorem.MeromorphicPeriodRelation
import HodgeLean.Foundations.Curves.AbelTheorem.NullCycleDualPrimitive
import HodgeLean.Foundations.Curves.AbelTheorem.IntegralPrimitiveValues
import HodgeLean.Foundations.Curves.AbelTheorem.ComplexIntegrationBasis

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold MeasureTheory
open scoped Topology ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [MeasurableSpace E] [BorelSpace E]
attribute [local instance] b3Forms_isManifold_real

theorem meromorphic_periods_of_null_cycle_dual_data (h : Module.finrank ℂ E = 1)
    (D : C →₀ ℤ) (hdeg : b4c_deg D = 0) (w : b4c_MeroForm E C h)
    (hr : ∀ x, b4c_res (hE := h) w x = (D x : ℂ))
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0)
    (p : C) (paths : C → ℝ → C)
    (hp : ∀ x, b3A_IsGoodPath (E := E) (paths x) p x)
    {ι : Type} [Fintype ι] (γ : ι → b3_SmoothLoop E C)
    (η : ι → C → E [⋀^Fin 1]→L[ℝ] ℝ) (hη : ∀ i, b3Forms_IsSmooth (η i))
    (hzero : ∀ i x, x ∈ D.support → η i =ᶠ[𝓝 x] 0)
    (hdual : ∀ i, ∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ,
      b3Forms_IsSmooth α → b3Forms_d α = 0 →
        b3Forms_integral (b3Rest_b h) (b3Forms_wedgeForm α (η i)) =
          b3Forms_lineIntegral α (γ i).val 0 1)
    (hpair : ∀ (P : ℂ →L[ℝ] ℝ) i, b3Forms_integral (b3Rest_b h)
      (b3Forms_wedgeForm (b4c_residue_realForm h (b4c_residue_normalizedForm h w) P) (η i)) =
        P (loopIntegral (γ i) w))
    (hint : ∀ i x, x ∈ D.support → ∃ m : ℤ,
      b3Forms_lineIntegral (η i) (paths x) 0 1 = (m : ℝ))
    (n : ι → ℤ) (hcycle : ∑ i, n i • b3_latticePeriod E C (γ i) = 0) :
    ∃ N : ℤ, ∑ i, (n i : ℂ) * loopIntegral (γ i) w =
      (2 * Real.pi * Complex.I) * (N : ℂ) := by
  obtain ⟨f, hf, hdf⟩ := primitive_of_integral_null_cycle_duals h γ η hη hdual n hcycle
  obtain ⟨N, hN⟩ := integral_divisor_values_of_primitive D hdeg p paths hp η hη n hint f hf hdf
  refine ⟨N, meromorphic_period_relation_of_dual_primitive h D w hr ha η hη hzero n f
    hf hdf (fun i => loopIntegral (γ i) w) ?_ N hN⟩
  intro P i
  rw [integral_eq_of_positive_basis_change (b3Rest_b h) (b4c_residue_basis h)
    (complex_integration_basis_change_positive h)]
  exact hpair P i

end HodgeLean.Foundations.Curves.AbelTheorem
