import HodgeLean.Foundations.Singular.RationalTensorCohomology
import HodgeLean.Foundations.Singular.ProductCohomologyComparison
import HodgeLean.Foundations.Singular.SingularShortDegreeSum
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CochainCohomologyEquiv

/-! Actual rational product cohomology compared with the finite sum of tensor factor cohomologies. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
open scoped TensorProduct DirectSum
namespace HodgeLean.Foundations.Singular

/-- The rational product-cohomology equivalence with one factor having finite cohomology in each degree.
Source: Hatcher, Algebraic Topology, §3.2, the field-coefficient cohomology Künneth theorem. -/
def rationalProductCohomologyEquiv (X Y : TopCat.{0})
    (hX : ∀ p : ℕ, Module.Finite ℚ (AlgebraicTopology.Singular.Cohomology ℚ X p)) (n : ℕ) :
    (⨁ a : tensorDegreeIndex n,
      AlgebraicTopology.Singular.Cohomology ℚ X a.1.1 ⊗[ℚ]
        AlgebraicTopology.Singular.Cohomology ℚ Y a.1.2) ≃ₗ[ℚ]
      AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (X × Y)) n := by
  letI (p : ℕ) : Module.Finite ℚ (AlgebraicTopology.Singular.Cohomology ℚ X p) := hX p
  have hK (p : ℕ) : Module.Finite ℚ ((rationalChains X).sc p).linearDual.homology :=
    Module.Finite.of_surjective
      (AlgebraicTopology.Singular.cochainCohomologyEquiv ℚ X p).symm.toLinearMap
      (AlgebraicTopology.Singular.cochainCohomologyEquiv ℚ X p).symm.surjective
  exact (singularShortDegreeSumEquiv X Y n).trans
    ((rationalTensorCohomologyEquiv (rationalChains X) (rationalChains Y) hK n).trans
      ((rationalProductTensorCohomologyEquiv X Y n).symm.trans
        (AlgebraicTopology.Singular.cochainCohomologyEquiv ℚ (TopCat.of (X × Y)) n)))

#print axioms rationalProductCohomologyEquiv
end HodgeLean.Foundations.Singular
