import HodgeLean.Foundations.Program.SchoenSelectedGeometryAbelJacobiRational
import HodgeLean.Foundations.Program.SchoenSelectedGeometryTorusRank
import HodgeLean.Foundations.Program.CurveJacobian

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- Abel–Jacobi pullback is bijective on rational degree-one cohomology. -/
theorem s0_abelJacobi_rational_pullback_bijective
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [Module.Finite ℤ (b3_periodLattice E C)]
    [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]
    (hE : Module.finrank ℂ E = 1) (p₀ : C)
    (aj : C → b3_Jacobian E C) (haj : b3_IsAbelJacobi E C p₀ aj) (hajc : Continuous aj) :
    Function.Bijective (cohomologyMap ℚ 1 (TopCat.ofHom ⟨aj, hajc⟩)) := by
  letI : Module.Free ℤ (b3_periodLattice E C) := b3_periodLattice_free
  obtain ⟨hfin, hrank⟩ := s0_weightOne_torus_first_betti
    (b3_periodLattice E C) (b3_periodF E C) (b3_isWeightOne hE)
  letI := hfin
  have hd : Module.finrank ℚ (Cohomology ℚ (TopCat.of (b3_Jacobian E C)) 1) =
      Module.finrank ℚ (Cohomology ℚ (TopCat.of C) 1) := by
    rw [hrank, b3_finrank_periodLattice hE, b3_finrank_cohomology hE]
  have hs := s0_abelJacobi_rational_pullback_surjective hE p₀ aj haj hajc
  letI := Module.Finite.of_surjective (cohomologyMap ℚ 1 (TopCat.ofHom ⟨aj, hajc⟩)) hs
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hs, hs⟩

#print axioms s0_abelJacobi_rational_pullback_bijective
end HodgeLean.Foundations.Program
