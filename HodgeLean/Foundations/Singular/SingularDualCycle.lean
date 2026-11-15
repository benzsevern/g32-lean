import HodgeLean.Foundations.Singular.Cup
import HodgeLean.Foundations.Singular.ProductNaturality
import HodgeConjecture.Lemmas.Algebra.Homology.LinearDualNaturality

/-! Actual singular cocycles in the reversed-dual short-complex model. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Simplicial
open scoped Simplicial
namespace HodgeLean.Foundations.Singular

/-- View a closed actual singular cochain as a cycle of the actual reversed-dual short complex.
Source: Hatcher, Algebraic Topology, §3.1, singular cocycles and cohomology classes. -/
def singularDualCycle (X : TopCat.{0}) (n : ℕ) :
    Cocycle ℚ (TopCat.toSSet.obj X) n →ₗ[ℚ] LinearMap.ker ((rationalChains X).sc n).f.hom.dualMap where
  toFun φ := ⟨φ.1, by
    change ((rationalChains X).d ((ComplexShape.down ℕ).prev n) n).hom.dualMap φ.1 = 0
    rw [ChainComplex.prev]
    exact φ.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual short-complex class of a singular cocycle is its specified singular cohomology class.
Source: Hatcher, Algebraic Topology, §3.1, singular cohomology as cocycles modulo coboundaries. -/
theorem singularDualCycle_class (X : TopCat.{0}) (n : ℕ)
    (φ : Cocycle ℚ (TopCat.toSSet.obj X) n) :
    AlgebraicTopology.Singular.cochainCohomologyEquiv ℚ X n
      (((rationalChains X).sc n).linearDual.moduleCatHomologyClass (singularDualCycle X n φ)) =
        cohomologyClass X n φ := by
  rfl

#print axioms singularDualCycle
#print axioms singularDualCycle_class
end HodgeLean.Foundations.Singular
