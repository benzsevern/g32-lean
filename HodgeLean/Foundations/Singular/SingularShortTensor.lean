import HodgeLean.Foundations.Singular.SingularDualCycle
import HodgeLean.Foundations.Singular.TensorSeparation

/-! Factorwise conversion of actual singular tensor classes to short-complex tensor classes. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- The actual factorwise tensor conversion from singular cohomology to its short-complex model.
Source: Hatcher, Algebraic Topology, §3.1, cohomology as cocycles modulo coboundaries. -/
def singularShortTensorEquiv (X Y : TopCat.{0}) (p q : ℕ) :
    (AlgebraicTopology.Singular.Cohomology ℚ X p ⊗[ℚ] AlgebraicTopology.Singular.Cohomology ℚ Y q) ≃ₗ[ℚ]
      (((rationalChains X).sc p).linearDual.homology ⊗[ℚ] ((rationalChains Y).sc q).linearDual.homology) :=
  TensorProduct.congr (AlgebraicTopology.Singular.cochainCohomologyEquiv ℚ X p).symm
    (AlgebraicTopology.Singular.cochainCohomologyEquiv ℚ Y q).symm

/-- The actual tensor conversion sends represented singular classes to their actual short-complex classes.
Source: Hatcher, Algebraic Topology, §3.1, cohomology as cocycles modulo coboundaries. -/
theorem singularShortTensorEquiv_classes (X Y : TopCat.{0}) (p q : ℕ)
    (φ : Cocycle ℚ (TopCat.toSSet.obj X) p) (ψ : Cocycle ℚ (TopCat.toSSet.obj Y) q) :
    singularShortTensorEquiv X Y p q (cohomologyClass X p φ ⊗ₜ[ℚ] cohomologyClass Y q ψ) =
      ((rationalChains X).sc p).linearDual.moduleCatHomologyClass (singularDualCycle X p φ) ⊗ₜ[ℚ]
        ((rationalChains Y).sc q).linearDual.moduleCatHomologyClass (singularDualCycle Y q ψ) := by
  have hφ := (LinearEquiv.symm_apply_eq (AlgebraicTopology.Singular.cochainCohomologyEquiv ℚ X p)).mpr
    (singularDualCycle_class X p φ).symm
  have hψ := (LinearEquiv.symm_apply_eq (AlgebraicTopology.Singular.cochainCohomologyEquiv ℚ Y q)).mpr
    (singularDualCycle_class Y q ψ).symm
  exact (TensorProduct.congr_tmul (AlgebraicTopology.Singular.cochainCohomologyEquiv ℚ X p).symm
    (AlgebraicTopology.Singular.cochainCohomologyEquiv ℚ Y q).symm _ _).trans
      (congrArg₂ (fun u v => u ⊗ₜ[ℚ] v) hφ hψ)

#print axioms singularShortTensorEquiv
#print axioms singularShortTensorEquiv_classes
end HodgeLean.Foundations.Singular
