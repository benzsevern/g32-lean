import HodgeLean.Foundations.Singular.TensorScalarCochain
import HodgeLean.Foundations.Singular.ProductAWComponents

/-! The specified topological projection-cup cochain as an actual Alexander–Whitney pullback. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- Pullback of the canonical actual scalar tensor cochain along Alexander–Whitney is the projection-cup cochain.
Source: Hatcher, Algebraic Topology, §3.2, the cochain cross product and Alexander–Whitney formula. -/
theorem tensorScalarCochain_AW (X Y : TopCat.{0}) (p q : ℕ)
    (φ : Module.Dual ℚ ((rationalChains X).X p)) (ψ : Module.Dual ℚ ((rationalChains Y).X q)) :
    (tensorScalarCochain (rationalChains X) (rationalChains Y) p q φ ψ).comp
        (productAlexanderWhitneyDegree X Y (p + q)) =
      cupCochain (TopCat.of (X × Y)) p q
        (cochainMap ℚ (TopCat.toSSet.map (productFirst X Y)) p φ)
        (cochainMap ℚ (TopCat.toSSet.map (productSecond X Y)) q ψ) := by
  change (tensorScalarPairing φ ψ).comp
    ((tensorChainProjection X Y p q (p + q)).hom.comp
      (productAlexanderWhitneyDegree X Y (p + q))) = _
  rw [productAlexanderWhitneyDegree_projection_sum]
  exact productFaceComponent_pairing X Y p q φ ψ

#print axioms tensorScalarCochain_AW
end HodgeLean.Foundations.Singular
