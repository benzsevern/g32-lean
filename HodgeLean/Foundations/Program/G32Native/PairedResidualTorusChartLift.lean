import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.TorusLocalLift
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AnalyticMap

/-! # Covering lifts in native charts of smooth complex schemes -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open scoped TensorProduct BigOperators Topology Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- A holomorphic map to the original period torus lifts analytically in each
native source chart, retaining its actual covering equation.
Source: Forster, Lectures on Riemann Surfaces, §21. -/
theorem residual_torus_native_chart_lift
    (X : Over (Spec ↧ℂ)) (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    {L : Type} [AddCommGroup L] [Module.Finite ℤ L]
    (F : Submodule ℂ (ℂ ⊗[ℤ] L))
    [DiscreteTopology (b2_latticeMap L F).range]
    (s : ComplexPoint X → b2_torus L F)
    (hs : ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, b5_V L F) ω s)
    (x : ComplexPoint X) :
    ∃ g : (Fin n → ℂ) → b5_V L F,
      AnalyticAt ℂ g (localChart X n x x) ∧
      ∀ᶠ w in 𝓝 x, b2_torusCover L F (g (localChart X n x w)) = s w := by
  let C := localChart X n x
  let A := s ∘ C.symm
  have hA : ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, b5_V L F) ω A (C x) := by
    have hh := contMDiffAt_iff_source.mp (hs x)
    change ContMDiffWithinAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, b5_V L F) ω A
      (Set.range 𝓘(ℂ, Fin n → ℂ)) (C x) at hh
    simpa only [modelWithCornersSelf_coe, Set.range_id, contMDiffWithinAt_univ] using hh
  obtain ⟨g, hg, he⟩ := torus_localLift F A (C x) hA
  refine ⟨g, hg.contDiffAt.analyticAt, ?_⟩
  have hx : x ∈ C.source := mem_localChart_source _ _ _
  filter_upwards [(C.continuousAt hx).eventually he, C.open_source.mem_nhds hx] with w hw hwC
  exact hw.symm.trans (congrArg s (C.left_inv hwC))

#print axioms residual_torus_native_chart_lift
end HodgeLean.Foundations.Program.G32Native
