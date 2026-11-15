import HodgeLean.Foundations.Program.SchoenSelectedGeometryIntegrationIndependent

noncomputable section
set_option maxHeartbeats 200000

open CategoryTheory HodgeLean.Adapters HodgeLean.Foundations
open AlgebraicTopology.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- Abel–Jacobi pullback surjects onto complex degree-one cohomology of the curve. -/
theorem s0_abelJacobi_complex_pullback_surjective
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [Module.Finite ℤ (b3_periodLattice E C)]
    [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]
    (hE : Module.finrank ℂ E = 1) (p₀ : C)
    (aj : C → b3_Jacobian E C) (haj : b3_IsAbelJacobi E C p₀ aj) (hajc : Continuous aj) :
    Function.Surjective (cohomologyMap ℂ 1 (TopCat.ofHom ⟨aj, hajc⟩)) := by
  classical
  letI : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  letI : Module.Finite ℚ (Cohomology ℚ (TopCat.of C) 1) :=
    (b3Rest2_finrank_cohomology_le (C := C) hE).1
  obtain ⟨hfin, hrk⟩ := spec_finrank_complexSingular_of_finite_aux (TopCat.of C) 1 inferInstance
  letI : Module.Finite ℂ (Cohomology ℂ (TopCat.of C) 1) := hfin
  letI : Module.Finite ℝ (b3_HolForm E C) := b3Forms_holForm_finiteDimensional_real (C := C) hE
  let b := Module.finBasis ℝ (b3_HolForm E C)
  let x := fun j ↦ Singular.cohomologyClass (TopCat.of C) 1
    (b3Rest2_integCocycle aj hajc b3Rest2_gre (b j))
  have hli : LinearIndependent ℂ x := s0_integration_basis_independent hE p₀ aj haj hajc b
  let F := cohomologyMap ℂ 1 (TopCat.ofHom ⟨aj, hajc⟩)
  have hspan : Submodule.span ℂ (Set.range x) ≤ LinearMap.range F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact s0_integration_class_mem_abelJacobi_range aj hajc b3Rest2_gre (b j)
  have hdim : Module.finrank ℂ (Cohomology ℂ (TopCat.of C) 1) =
      Module.finrank ℝ (b3_HolForm E C) := by
    rw [hrk, b3Rest2_finrank_cohomology hE, finrank_real_of_complex]
  have htop := hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hdim])
  exact LinearMap.range_eq_top.mp (top_unique (htop ▸ hspan))

#print axioms s0_abelJacobi_complex_pullback_surjective
end HodgeLean.Foundations.Program
