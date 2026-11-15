import HodgeLean.Foundations.Program.RiemannRoch

noncomputable section
open HodgeLean.Foundations.Program
open Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Source: Forster, Lectures on Riemann Surfaces, §§10, 13, extension of scalar meromorphic representatives. -/
theorem meromorphicFunction_of_scalar_local_orders
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (h : Module.finrank ℂ E = 1) (D : C →₀ ℤ) (f : C → ℂ)
    (hf : ∀ x, MeromorphicAt (fun t : ℂ => f ((extChartAt 𝓘(ℂ, E) x).symm
      (extChartAt 𝓘(ℂ, E) x x + b4cov_lineEquiv h t))) 0)
    (hord : ∀ x, meromorphicOrderAt (fun t : ℂ => f ((extChartAt 𝓘(ℂ, E) x).symm
      (extChartAt 𝓘(ℂ, E) x x + b4cov_lineEquiv h t))) 0 = (D x : WithTop ℤ))
    (p : C) (hp : ContinuousAt f p) (hne : f p ≠ 0) :
    ∃ F : b4c_MeroFun E C, (∃ x, F x ≠ (0 : ℂ)) ∧ b4c_div E F = D := by
  obtain ⟨F, he, hv⟩ := RiemannRochAna_normalize_to_meroFun h f hf p hp
  have hnonzero : ∃ x, F x ≠ (0 : ℂ) := by
    refine ⟨p, ?_⟩
    rw [hv p hp]
    exact fun hz => hne (OnePoint.coe_injective hz)
  refine ⟨F, hnonzero, Finsupp.ext fun x => ?_⟩
  rw [RiemannRochAna_div_apply_of_finite F (b4c_meroFun_orderSupport_finite h F) x]
  have hl := RiemannRochAna_normalization_local_germ h f F x (he x)
  have ho := RiemannRochEichler_ord_eq_local h F hnonzero x
  change ((b4c_ord E F x : ℤ) : WithTop ℤ) = meromorphicOrderAt
    (fun t : ℂ => (F ((extChartAt 𝓘(ℂ, E) x).symm
      (extChartAt 𝓘(ℂ, E) x x + b4cov_lineEquiv h t))).elim 0 id) 0 at ho
  rw [meromorphicOrderAt_congr hl, hord x] at ho
  exact WithTop.coe_injective ho

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
