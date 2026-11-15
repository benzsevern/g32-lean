import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.MeromorphicRegularTrace
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.MeromorphicTraceContinuity
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.TorusRemovable

noncomputable section
open HodgeLean.Foundations.Program
open scoped TensorProduct Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Source: Forster, Lectures on Riemann Surfaces, §§6, 17, 21, holomorphic trace along a finite map. -/
theorem meromorphicFiberSum_contMDiff
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (h : Module.finrank ℂ E = 1) (f : b4c_MeroFun E C) (hnc : ∃ x y, f x ≠ f y)
    {L : Type} [AddCommGroup L] [Module.Finite ℤ L]
    (F : Submodule ℂ (ℂ ⊗[ℤ] L)) [DiscreteTopology (b2_latticeMap L F).range]
    (a : C → b2_torus L F)
    (ha : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, b5_V L F) ω a) :
    letI := b4cov_sphChartedSpace
    letI := b4cov_sph_isManifold
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, b5_V L F) ω (meromorphicFiberSum h f hnc a) := by
  letI := b4cov_sphChartedSpace
  letI := b4cov_sph_isManifold
  apply torus_holomorphic_of_finite_exceptional F (meromorphicFiberSum h f hnc a)
    (meromorphicFiberSum_continuous h f hnc a ha.continuous)
    (meromorphicCriticalValues (E := E) f) (meromorphicCriticalValues_finite h f hnc)
  intro z hz
  exact meromorphicFiberSum_holomorphicAt_regular h f hnc F a ha z hz

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
