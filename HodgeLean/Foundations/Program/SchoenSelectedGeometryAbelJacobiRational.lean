import HodgeLean.Foundations.Program.SchoenSelectedGeometryAbelJacobiSurjective
import HodgeLean.Foundations.Program.SchoenSelectedGeometryRationalSurjectivity

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- Abel–Jacobi pullback surjects onto rational degree-one cohomology of the curve. -/
theorem s0_abelJacobi_rational_pullback_surjective
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [Module.Finite ℤ (b3_periodLattice E C)]
    [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]
    (hE : Module.finrank ℂ E = 1) (p₀ : C)
    (aj : C → b3_Jacobian E C) (haj : b3_IsAbelJacobi E C p₀ aj) (hajc : Continuous aj) :
    Function.Surjective (cohomologyMap ℚ 1 (TopCat.ofHom ⟨aj, hajc⟩)) := by
  exact s0_rational_pullback_surjective_of_complex 1 _
    (s0_abelJacobi_complex_pullback_surjective hE p₀ aj haj hajc)

#print axioms s0_abelJacobi_rational_pullback_surjective
end HodgeLean.Foundations.Program
