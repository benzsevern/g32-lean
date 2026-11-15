import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.RamifiedFibers
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.SphereTorus

noncomputable section
open HodgeLean.Foundations.Program
open scoped TensorProduct Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Source: Forster, Lectures on Riemann Surfaces, §§17, 21, Abel theorem via fiber sums. -/
theorem meromorphic_divisor_sum_zero_of_fiber_holomorphic
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (h : Module.finrank ℂ E = 1) (f : b4c_MeroFun E C)
    (hnc : ∃ x y, f x ≠ f y)
    (M : Type) [AddCommGroup M] [Module.Finite ℤ M] [Module.Free ℤ M]
    (G : Submodule ℂ (ℂ ⊗[ℤ] M)) (hG : b2_IsWeightOne M G)
    [DiscreteTopology (b2_latticeMap M G).range]
    (a : C → b2_torus M G)
    (htrace : letI := b4cov_sphChartedSpace
      letI := b4cov_sph_isManifold
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, b5_V M G) ω (meromorphicFiberSum h f hnc a)) :
    weightedSum a (b4c_div E f) = 0 := by
  have hc := sphere_torusMap_constant M G hG (meromorphicFiberSum h f hnc a) htrace
    ((0 : ℂ) : OnePoint ℂ) OnePoint.infty
  exact (meromorphic_divisor_sum_eq_fiberDifference h f hnc a).trans (sub_eq_zero.mpr hc)

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
