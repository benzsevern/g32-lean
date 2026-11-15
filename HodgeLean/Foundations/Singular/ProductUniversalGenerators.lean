import HodgeLean.Foundations.Singular.ProductModelExtensions

/-! Universal representatives of the actual tensor simplex generators. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- The tensor of the two actual identity simplices in its specified total degree.
Source: Hatcher, Algebraic Topology, §3.2, universal simplex-product models. -/
def universalTensorSimplex (p q n : ℕ) (hpq : p + q = n) :
    (rationalTensorChains
      (TopCat.of (Convexity.StdSimplex ℝ (Fin (p + 1))))
      (TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1))))).X n :=
  (tensorChainInclusion _ _ p q n hpq).hom
    (chainOfSimplex ℚ (standardTopologicalSimplexIdentitySimplex p) ⊗ₜ[ℚ]
      chainOfSimplex ℚ (standardTopologicalSimplexIdentitySimplex q))

/-- Every actual tensor simplex generator is the image of its universal identity pair.
Source: Hatcher, Algebraic Topology, §3.2, universal simplex-product models. -/
theorem universalTensorSimplex_map (X Y : TopCat.{0}) (p q n : ℕ) (hpq : p + q = n)
    (σ : (TopCat.toSSet.obj X) _⦋p⦌) (τ : (TopCat.toSSet.obj Y) _⦋q⦌) :
    ((rationalTensorChainMap (singularSimplexTopCatMap X p σ)
      (singularSimplexTopCatMap Y q τ)).f n).hom (universalTensorSimplex p q n hpq) =
      (tensorChainInclusion X Y p q n hpq).hom
        (chainOfSimplex ℚ σ ⊗ₜ[ℚ] chainOfSimplex ℚ τ) := by
  unfold universalTensorSimplex
  erw [rationalTensorChainMap_simplex,
    standardTopologicalSimplexIdentitySimplex_map,
    standardTopologicalSimplexIdentitySimplex_map]

#print axioms universalTensorSimplex
#print axioms universalTensorSimplex_map
end HodgeLean.Foundations.Singular
