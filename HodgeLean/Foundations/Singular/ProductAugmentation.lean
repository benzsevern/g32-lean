import HodgeLean.Foundations.Singular.ProductZero

/-! The actual point map and the first boundary obstruction. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- The actual continuous map to the singleton used by the chain contraction.
Source: Hatcher, Algebraic Topology, §2.1, the augmentation to a point. -/
def productPointMap (X : TopCat.{0}) : X ⟶ TopCat.of (ULift.{0} Unit) :=
  TopCat.ofHom ⟨fun _ => ⟨()⟩, continuous_const⟩

/-- The point map of a product factors through the two actual factor point maps.
Source: Hatcher, Algebraic Topology, §3.2, naturality of products and augmentation. -/
theorem productPointMap_factor (X Y : TopCat.{0}) :
    productPointMap (TopCat.of (X × Y)) =
      topologicalProductMap (productPointMap X) (productPointMap Y) ≫
        productPointMap (TopCat.of (ULift.{0} Unit × ULift.{0} Unit)) := by
  ext x

/-- The contraction's chain map to a point is the chain map of the actual unique point map.
Source: Hatcher, Algebraic Topology, Theorem 2.10, chain homotopy of a contraction. -/
theorem contractible_chain_point_map_eq
    (X : Type) [TopologicalSpace X] [ContractibleSpace X] :
    (AlgebraicTopology.contractibleSingularChainHomotopyEquiv ℚ X).hom =
      rationalChainMap (productPointMap (TopCat.of X)) := by
  let F := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  change F.map _ = F.map _
  congr 1

/-- An actual zero-degree chain in the kernel of the point map has a filler on a contractible space.
Source: Hatcher, Algebraic Topology, Theorem 2.10, chain homotopy of a contraction. -/
theorem contractible_zero_cycle_filler_of_point_map
    (X : Type) [TopologicalSpace X] [ContractibleSpace X]
    (z : (rationalChains (TopCat.of X)).X 0)
    (hz : ((rationalChainMap (productPointMap (TopCat.of X))).f 0).hom z = 0) :
    ∃ w : (rationalChains (TopCat.of X)).X 1,
      ((rationalChains (TopCat.of X)).d 1 0).hom w = z := by
  apply contractible_zero_cycle_filler X z
  rw [contractible_chain_point_map_eq]
  exact hz

/-- The first cross-product obstruction is annihilated by the actual point map.
Source: Hatcher, Algebraic Topology, §3.2, augmentation of the tensor cross product. -/
theorem tensorProductZero_point_boundary (X Y : TopCat.{0})
    (z : (rationalTensorChains X Y).X 1) :
    ((rationalChainMap (productPointMap (TopCat.of (X × Y)))).f 0).hom
      (tensorProductZero X Y (((rationalTensorChains X Y).d 1 0).hom z)) = 0 := by
  rw [productPointMap_factor X Y, rationalChainMap_comp_apply]
  have hn := LinearMap.congr_fun
    (tensorProductZero_naturality (productPointMap X) (productPointMap Y))
      (((rationalTensorChains X Y).d 1 0).hom z)
  simp only [LinearMap.comp_apply] at hn
  rw [← hn, ← rationalTensorChainMap_boundary (productPointMap X) (productPointMap Y) 1 0 z]
  rw [rationalTensorChain_boundary_one_of_subsingleton (ULift.{0} Unit) (ULift.{0} Unit),
    LinearMap.zero_apply, map_zero, map_zero]

#print axioms tensorProductZero_point_boundary
#print axioms contractible_zero_cycle_filler_of_point_map
#print axioms contractible_chain_point_map_eq
#print axioms productPointMap
#print axioms productPointMap_factor
end HodgeLean.Foundations.Singular
