import HodgeLean.Foundations.IntegralHomology.Defs
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CochainCohomologyEquiv
import Mathlib.LinearAlgebra.Basis.Defs

/-! Finite integral chain models and degree-one evaluation on actual singular classes.
The model records chain and homotopy data; finiteness of homology is a separate assertion.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.IntegralHomology.StageTwo

/-- A bounded finite free integral chain model with an actual singular comparison.
Source: Hatcher, Algebraic Topology, §2.1, simplicial and singular homology, and §2.2, cellular homology. -/
structure FiniteChainModel (X : TopCat.{0}) where
  chains : ChainComplex (ModuleCat.{0} ℤ) ℕ
  rank : ℕ → ℕ
  basis : ∀ n, Module.Basis (Fin (rank n)) ℤ (chains.X n)
  dimension : ℕ
  bounded : ∀ n, dimension < n → rank n = 0
  comparison : HomotopyEquiv chains (ZChains X)

example (X : TopCat.{0}) (M : FiniteChainModel X) (n : ℕ) :
    (Fin (M.rank n) → ℤ) ≃ₗ[ℤ] M.chains.X n := (M.basis n).equivFun.symm

/-- Evaluation of actual singular cohomology on actual homology, in degree one.
This construction uses quotient evaluation over any commutative coefficient ring.
Source: Hatcher, Algebraic Topology, §3.1, the Kronecker pairing;
ShortComplex.dualHomologyComparisonExplicit. -/
def evaluation (R : Type) [CommRing R] (X : TopCat.{0}) :
    Cohomology R X 1 →ₗ[R] Module.Dual R (Homology R X 1) :=
  let S := (SingularChainComplex R X).sc 1
  S.moduleCatHomologyIso.toLinearEquiv.dualMap.toLinearMap.comp <|
    S.dualHomologyComparisonExplicit.comp <|
      S.linearDual.moduleCatHomologyIso.toLinearEquiv.toLinearMap.comp
        (cochainCohomologyEquiv R X 1).symm.toLinearMap

example (R : Type) [CommRing R] (X : TopCat.{0})
    (u : Cohomology R X 1) : evaluation R X u 0 = 0 := map_zero _

/-- Precomposition of functionals with the actual lattice pushforward.
Source: Hatcher, Algebraic Topology, §3.1, naturality of evaluation. -/
def latticeDualPullback {X Y : TopCat.{0}} (f : X ⟶ Y) :
    Module.Dual ℤ (Lattice Y) →ₗ[ℤ] Module.Dual ℤ (Lattice X) :=
  (mapLattice f).dualMap

example {X Y : TopCat.{0}} (f : X ⟶ Y)
    (u : Module.Dual ℤ (Lattice Y)) (a : Lattice X) :
    latticeDualPullback f u a = u (mapLattice f a) := rfl

example : (2 • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)).dualMap
    (LinearMap.id : Module.Dual ℤ ℤ) 3 = 6 := rfl

end HodgeLean.Foundations.IntegralHomology.StageTwo
