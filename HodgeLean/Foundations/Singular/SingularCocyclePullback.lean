import HodgeLean.Foundations.Singular.SingularDualCycle

/-! Actual singular cocycle pullbacks through reversed-dual short-complex maps. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Simplicial
open scoped Simplicial
namespace HodgeLean.Foundations.Singular

/-- Pull back an actual singular cocycle using its actual reversed-dual chain map.
Source: Hatcher, Algebraic Topology, §3.1, functoriality of singular cohomology. -/
def singularCocyclePullback {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (φ : Cocycle ℚ (TopCat.toSSet.obj Y) n) : Cocycle ℚ (TopCat.toSSet.obj X) n :=
  cohomologyCycleToCocycle ℚ n (ShortComplex.moduleCatCycleMap
    (ShortComplex.linearDualMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map
        (rationalChainMap f))) (singularDualCycle Y n φ))

/-- The actual singular cocycle pullback represents the specified induced cohomology class.
Source: Hatcher, Algebraic Topology, §3.1, functoriality of singular cohomology. -/
theorem singularCocyclePullback_class {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (φ : Cocycle ℚ (TopCat.toSSet.obj Y) n) :
    AlgebraicTopology.Singular.cohomologyMap ℚ n f (cohomologyClass Y n φ) =
      cohomologyClass X n (singularCocyclePullback f n φ) :=
  cohomologyMap_class Y f n φ (singularCocyclePullback f n φ) rfl

#print axioms singularCocyclePullback
#print axioms singularCocyclePullback_class
end HodgeLean.Foundations.Singular
