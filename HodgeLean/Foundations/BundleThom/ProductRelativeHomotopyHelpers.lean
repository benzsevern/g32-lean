import HodgeLean.Foundations.BundleThom.ProductContractionHelpers
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.LocalHomologyVanishing

/-! # Actual relative chain reduction along a supplied base contraction

Projection and the specified fibre inclusion remain the two maps of the chain homotopy equivalence.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- A supplied contraction of the base induces an actual chain homotopy equivalence with the punctured normal pair.
Source: Hatcher, Algebraic Topology, §2.1, relative homotopy invariance. -/
def i1_productNormalRelativeChainHomotopyEquiv {B : Type} [TopologicalSpace B] (k : ℕ) (b : B)
    (H : ContinuousMap.Homotopy (ContinuousMap.const B b) (ContinuousMap.id B)) :
    HomotopyEquiv ((relativeChainFunctor ℚ).obj (i1_productNormalPair B k))
      ((relativeChainFunctor ℚ).obj (puncturedPair ℂ k)) where
  hom := (relativeChainFunctor ℚ).map (i1_productNormalProjection B k)
  inv := (relativeChainFunctor ℚ).map (i1_productNormalSection k b)
  homotopyHomInvId :=
    (Homotopy.ofEq ((relativeChainFunctor ℚ).map_comp
        (i1_productNormalProjection B k) (i1_productNormalSection k b)).symm).trans
      (((i1_productNormalContraction k b H).relativeChainHomotopy (R := ℚ)).trans
        (Homotopy.ofEq ((relativeChainFunctor ℚ).map_id (i1_productNormalPair B k))))
  homotopyInvHomId := Homotopy.ofEq (by
    rw [← CategoryTheory.Functor.map_comp, i1_productNormalSection_projection,
      CategoryTheory.Functor.map_id])

/-- The actual normal projection identifies every relative homology degree after a supplied base contraction.
Source: Hatcher, Algebraic Topology, §2.1, relative homotopy invariance. -/
def i1_productNormalRelativeHomologyIso {B : Type} [TopologicalSpace B] (k : ℕ) (b : B)
    (H : ContinuousMap.Homotopy (ContinuousMap.const B b) (ContinuousMap.id B)) (n : ℕ) :
    RelativeHomology ℚ (i1_productNormalPair B k) n ≅ RelativeHomology ℚ (puncturedPair ℂ k) n :=
  (i1_productNormalRelativeChainHomotopyEquiv k b H).toHomologyIso n

/-- The product relative homology vanishes off twice the complex rank when a base contraction is supplied.
Source: Hatcher, Algebraic Topology, §2.2, homology of the punctured Euclidean pair. -/
theorem i1_productNormalRelativeHomology_isZero_of_contraction {B : Type} [TopologicalSpace B]
    (k : ℕ) (b : B) (H : ContinuousMap.Homotopy (ContinuousMap.const B b) (ContinuousMap.id B))
    (n : ℕ) (hn : n ≠ 2 * k) : IsZero (RelativeHomology ℚ (i1_productNormalPair B k) n) :=
  (standardComplexLocalHomology_isZero_of_ne k n hn).of_iso
    (i1_productNormalRelativeHomologyIso k b H n)

end HodgeLean.Foundations.BundleThom
