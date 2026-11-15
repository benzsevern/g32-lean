import HodgeLean.Foundations.Curves.AbelTheorem.IntegralMeromorphicDual
import HodgeLean.Foundations.Curves.AbelTheorem.FiniteTransverseDivisorPaths
import HodgeLean.Foundations.Curves.AbelTheorem.NullCycleMeromorphicPeriods

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

theorem integral_meromorphic_periods_of_null_cycle (h : Module.finrank ℂ E = 1)
    (D : C →₀ ℤ) (hdeg : b4c_deg D = 0) (w : b4c_MeroForm E C h)
    (hr : ∀ x, b4c_res (hE := h) w x = (D x : ℂ))
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0)
    {ι : Type} [Fintype ι] (γ : ι → b3_SmoothLoop E C)
    (hav : ∀ i t, (γ i).val t ∉ D.support)
    (n : ι → ℤ) (hcycle : ∑ i, n i • b3_latticePeriod E C (γ i) = 0) :
    ∃ N : ℤ, ∑ i, (n i : ℂ) * loopIntegral (γ i) w =
      (2 * Real.pi * Complex.I) * (N : ℂ) := by
  classical
  obtain ⟨p, paths, hp, hbound, hpoff, htr⟩ :=
    exists_divisor_paths_transverse_to_finite_loops h D γ hav
  have hη i := exists_integral_meromorphic_dual h D w ha (γ i) (hav i)
    (fun x : D.support => paths x.val) (fun x => (hp x.val).1)
    (fun x => hbound x.val) (fun x => htr i x.val x.property)
    (fun x s => by
      rw [(hp x.val).apply_zero, (hp x.val).apply_one]
      exact ⟨hpoff i s, fun he => hav i s (he ▸ x.property)⟩)
  choose η hs hz hint hdual hpair using hη
  exact meromorphic_periods_of_null_cycle_dual_data h D hdeg w hr ha p paths hp γ η
    hs hz hdual (fun P i => hpair i P) (fun i x hx => hint i ⟨x, hx⟩) n hcycle

end HodgeLean.Foundations.Curves.AbelTheorem
