import HodgeLean.Foundations.Singular.ProductTruncation

/-! The natural tensor-to-product comparison on actual rational singular chains. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- Recursively extend the actual finite-degree comparison maps.
Source: Hatcher, Algebraic Topology, §3.2, the acyclic-models construction. -/
def productChainTruncations : (n : ℕ) → ProductChainTruncation (n + 1)
  | 0 => productChainTruncationOne
  | n + 1 => ProductChainTruncation.extend n (productChainTruncations n)

/-- The actual tensor-to-product comparison in one degree, from its compatible truncation.
Source: Hatcher, Algebraic Topology, §3.2, the acyclic-models construction. -/
def tensorProductDegreeMap (X Y : TopCat.{0}) (n : ℕ) :
    (rationalTensorChains X Y).X n →ₗ[ℚ] (rationalChains (TopCat.of (X × Y))).X n :=
  (productChainTruncations n).map n (Nat.le_succ n) X Y

/-- The constructed actual comparison is natural in each degree.
Source: Hatcher, Algebraic Topology, §3.2, the acyclic-models construction. -/
theorem tensorProductDegreeMap_naturality
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) :
    (tensorProductDegreeMap X' Y' n).comp ((rationalTensorChainMap f g).f n).hom =
      (((rationalChainMap (topologicalProductMap f g)).f n).hom).comp
        (tensorProductDegreeMap X Y n) :=
  (productChainTruncations n).naturality n (Nat.le_succ n) f g

/-- The next degree map agrees with the last map in the preceding compatible truncation.
Source: Hatcher, Algebraic Topology, §3.2, induction of chain comparison maps. -/
theorem tensorProductDegreeMap_succ (X Y : TopCat.{0}) (n : ℕ) :
    tensorProductDegreeMap X Y (n + 1) =
      (productChainTruncations n).map (n + 1) (le_refl _) X Y :=
  ProductChainTruncation.extend_map_le n (productChainTruncations n) (n + 1)
    (le_refl _) (Nat.le_succ (n + 1)) X Y

/-- The constructed actual comparison commutes with the singular boundary in every degree.
Source: Hatcher, Algebraic Topology, §3.2, the acyclic-models construction. -/
theorem tensorProductDegreeMap_boundary (X Y : TopCat.{0}) (n : ℕ) :
    (((rationalChains (TopCat.of (X × Y))).d (n + 1) n).hom).comp
        (tensorProductDegreeMap X Y (n + 1)) =
      (tensorProductDegreeMap X Y n).comp ((rationalTensorChains X Y).d (n + 1) n).hom := by
  rw [tensorProductDegreeMap_succ]
  exact (productChainTruncations n).boundary n (le_refl _) X Y

/-- The actual rational tensor-to-product singular chain map constructed from universal model fillers.
Source: Hatcher, Algebraic Topology, §3.2, the acyclic-models construction. -/
def tensorProductComparison (X Y : TopCat.{0}) :
    rationalTensorChains X Y ⟶ rationalChains (TopCat.of (X × Y)) where
  f n := ModuleCat.ofHom (tensorProductDegreeMap X Y n)
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    apply ModuleCat.hom_ext
    exact tensorProductDegreeMap_boundary X Y j

/-- The actual tensor-to-product singular chain map is natural in both spaces.
Source: Hatcher, Algebraic Topology, §3.2, the acyclic-models construction. -/
theorem tensorProductComparison_naturality
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') :
    rationalTensorChainMap f g ≫ tensorProductComparison X' Y' =
      tensorProductComparison X Y ≫ rationalChainMap (topologicalProductMap f g) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  exact tensorProductDegreeMap_naturality f g n

/-- The actual comparison is the specified vertex-pairing map in degree zero.
Source: Hatcher, Algebraic Topology, §3.2, normalization of the cross product. -/
theorem tensorProductComparison_zero (X Y : TopCat.{0}) :
    ((tensorProductComparison X Y).f 0).hom = tensorProductZero X Y := rfl

#print axioms tensorProductComparison_zero
#print axioms tensorProductComparison_naturality
#print axioms tensorProductComparison
#print axioms tensorProductDegreeMap_boundary
#print axioms tensorProductDegreeMap_succ
#print axioms productChainTruncations
#print axioms tensorProductDegreeMap
#print axioms tensorProductDegreeMap_naturality
end HodgeLean.Foundations.Singular
