import HodgeLean.Foundations.Program.SchoenSelectedGeometryLiftCocycleNaturality
import HodgeLean.Foundations.Program.CurveJacobianRest2IntegCurve

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- Every period integration class lies in the pullback image from the analytic Jacobian. -/
theorem s0_integration_class_mem_abelJacobi_range
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [Module.Finite ℤ (b3_periodLattice E C)]
    [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]
    (aj : C → b3_Jacobian E C) (haj : Continuous aj)
    (g : ℂ →+ ℂ) (θ : b3_HolForm E C) :
    HodgeLean.Foundations.Singular.cohomologyClass (TopCat.of C) 1
        (b3Rest2_integCocycle aj haj g θ) ∈
      LinearMap.range (AlgebraicTopology.Singular.cohomologyMap ℂ 1 (TopCat.ofHom ⟨aj, haj⟩)) := by
  refine ⟨HodgeLean.Foundations.Singular.cohomologyClass (TopCat.of (b3_Jacobian E C)) 1
    (b3Rest2_liftCocycle b3Rest2_covHom b3Rest2_covHom_spec id continuous_id
      (g.comp (b3Rest2_ellV θ))), ?_⟩
  exact s0_lift_cohomology_comp b3Rest2_covHom b3Rest2_covHom_spec id continuous_id
    aj haj (g.comp (b3Rest2_ellV θ))

#print axioms s0_integration_class_mem_abelJacobi_range
end HodgeLean.Foundations.Program
