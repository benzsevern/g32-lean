import HodgeLean.Foundations.Program.RelativeTorusKernel
import HodgeLean.Foundations.Singular.TorusRing

noncomputable section
open AlgebraicTopology.Singular HodgeLean.Foundations.Singular
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- The first rational Betti dimension of a weight-one torus is its lattice rank. -/
theorem s0_weightOne_torus_first_betti
    (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (F : Submodule ℂ (ℂ ⊗[ℤ] L)) (hF : b2_IsWeightOne L F) :
    Module.Finite ℚ (Cohomology ℚ (TopCat.of (b2_torus L F)) 1) ∧
      Module.finrank ℚ (Cohomology ℚ (TopCat.of (b2_torus L F)) 1) =
        Module.finrank ℤ L := by
  obtain ⟨e, _⟩ := b2_torus_addEquiv (Module.finBasis ℤ L) F hF
  let E := cohomologyHomeomorphEquiv e.toHomeomorph 1
  letI := finite_cohomology_unitAddTorus (Module.finrank ℤ L) 1
  refine ⟨Module.Finite.of_injective E.toLinearMap E.injective, ?_⟩
  rw [E.finrank_eq, finrank_cohomology_one_unitAddTorus]

#print axioms s0_weightOne_torus_first_betti
end HodgeLean.Foundations.Program
