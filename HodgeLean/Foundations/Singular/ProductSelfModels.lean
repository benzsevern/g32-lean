import HodgeLean.Foundations.Singular.ProductVertexFaces
import HodgeLean.Foundations.Singular.ProductUniversalGenerators

/-! Universal diagonal product simplices for actual product-chain homotopies. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- The actual chain of the diagonal simplex in the product of two standard simplices.
Source: Hatcher, Algebraic Topology, §3.2, acyclic models for the Eilenberg–Zilber comparison. -/
def universalProductSimplex (n : ℕ) :
    (rationalChains (TopCat.of (simplexProductModel n n))).X n :=
  chainOfSimplex ℚ (pairedSimplex _ _ n (standardTopologicalSimplexIdentitySimplex n)
    (standardTopologicalSimplexIdentitySimplex n))

/-- The diagonal model simplex maps to the paired simplex specified by its two factor maps.
Source: Hatcher, Algebraic Topology, §3.2, acyclic models for the Eilenberg–Zilber comparison. -/
theorem universalProductSimplex_map (X Y : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (τ : (TopCat.toSSet.obj Y) _⦋n⦌) :
    ((rationalChainMap (simplexPairMap X Y n n σ τ)).f n).hom (universalProductSimplex n) =
      chainOfSimplex ℚ (pairedSimplex X Y n σ τ) := by
  unfold universalProductSimplex
  erw [rationalChainMap_simplex]
  unfold simplexPairMap
  rw [← pairedSimplex_naturality, standardTopologicalSimplexIdentitySimplex_map,
    standardTopologicalSimplexIdentitySimplex_map]

/-- The projected simplices of a mapped product simplex are the mapped factor simplices.
Source: Hatcher, Algebraic Topology, §3.2, naturality of products of singular simplices. -/
theorem productSimplexProjections_naturality
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ)
    (σ : (TopCat.toSSet.obj (TopCat.of (X × Y))) _⦋n⦌) :
    (TopCat.toSSet.map (productFirst X' Y')).app _
        ((TopCat.toSSet.map (topologicalProductMap f g)).app _ σ) =
      (TopCat.toSSet.map f).app _ ((TopCat.toSSet.map (productFirst X Y)).app _ σ) ∧
    (TopCat.toSSet.map (productSecond X' Y')).app _
        ((TopCat.toSSet.map (topologicalProductMap f g)).app _ σ) =
      (TopCat.toSSet.map g).app _ ((TopCat.toSSet.map (productSecond X Y)).app _ σ) := by
  constructor <;> apply (TopCat.toSSetObjEquiv _ _).injective <;> rfl

#print axioms productSimplexProjections_naturality
#print axioms universalProductSimplex
#print axioms universalProductSimplex_map
end HodgeLean.Foundations.Singular
