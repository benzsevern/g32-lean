import HodgeLean.Foundations.Singular.ProductVertexFaces

/-! The two actual comparison degree maps are inverse on vertices. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- The vertex cross product after the actual Alexander–Whitney map is the identity.
Source: Hatcher, Algebraic Topology, §3.2, the Eilenberg–Zilber comparison in degree zero. -/
theorem tensorProductZero_after_AW (X Y : TopCat.{0}) :
    (tensorProductZero X Y).comp (productAlexanderWhitneyDegree X Y 0) = LinearMap.id := by
  apply rationalChain_linearMap_ext (TopCat.of (X × Y)) 0
  intro σ
  change tensorProductZero X Y (productAlexanderWhitneyDegree X Y 0 (chainOfSimplex ℚ σ)) =
    chainOfSimplex ℚ σ
  erw [productAlexanderWhitneyDegree_vertex, tensorProductZero_simplex]
  exact congrArg (chainOfSimplex ℚ) (pairedSimplex_projections X Y 0 σ)

/-- The actual Alexander–Whitney map after the vertex cross product is the identity.
Source: Hatcher, Algebraic Topology, §3.2, the Eilenberg–Zilber comparison in degree zero. -/
theorem AW_after_tensorProductZero (X Y : TopCat.{0}) :
    (productAlexanderWhitneyDegree X Y 0).comp (tensorProductZero X Y) = LinearMap.id := by
  apply rationalTotalTensor_linearMap_ext X Y 0
  intro p q hpq σ τ
  have hp : p = 0 := by omega
  have hq : q = 0 := by omega
  subst p
  subst q
  change productAlexanderWhitneyDegree X Y 0
    (tensorProductZero X Y ((tensorChainInclusion X Y 0 0 0 rfl).hom
      (chainOfSimplex ℚ σ ⊗ₜ[ℚ] chainOfSimplex ℚ τ))) =
    (tensorChainInclusion X Y 0 0 0 rfl).hom
      (chainOfSimplex ℚ σ ⊗ₜ[ℚ] chainOfSimplex ℚ τ)
  erw [tensorProductZero_simplex, productAlexanderWhitneyDegree_vertex]
  rw [productFirst_pairedSimplex, productSecond_pairedSimplex]

#print axioms AW_after_tensorProductZero
#print axioms tensorProductZero_after_AW
end HodgeLean.Foundations.Singular
