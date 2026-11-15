import HodgeLean.Foundations.Singular.ProductSelfExtensions
import HodgeLean.Foundations.Singular.ProductSteps

/-! Boundary control for extensions from diagonal product models. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- A filler on the diagonal product model extends to a primitive of the specified natural product map.
Source: Hatcher, Algebraic Topology, §3.2, acyclic models for chain homotopies. -/
theorem productSelfModelExtension_boundary (n m : ℕ)
    (a : ∀ X Y : TopCat.{0}, (rationalChains (TopCat.of (X × Y))).X n →ₗ[ℚ]
      (rationalChains (TopCat.of (X × Y))).X m)
    (ha : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      (a X' Y').comp ((rationalChainMap (topologicalProductMap f g)).f n).hom =
        (((rationalChainMap (topologicalProductMap f g)).f m).hom).comp (a X Y))
    (c : (rationalChains (TopCat.of (simplexProductModel n n))).X (m + 1))
    (hc : ((rationalChains (TopCat.of (simplexProductModel n n))).d (m + 1) m).hom c =
      a (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1))))
        (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1)))) (universalProductSimplex n))
    (X Y : TopCat.{0}) :
    (((rationalChains (TopCat.of (X × Y))).d (m + 1) m).hom).comp
      (productSelfModelExtension X Y n (m + 1) c) = a X Y := by
  apply rationalChain_linearMap_ext (TopCat.of (X × Y)) n
  intro σ
  erw [LinearMap.comp_apply, productSelfModelExtension_simplex,
    rationalChainMap_boundary, hc]
  let σ₁ := (TopCat.toSSet.map (productFirst X Y)).app _ σ
  let σ₂ := (TopCat.toSSet.map (productSecond X Y)).app _ σ
  let f := singularSimplexTopCatMap X n σ₁
  let g := singularSimplexTopCatMap Y n σ₂
  let u := universalProductSimplex n
  have hn := LinearMap.congr_fun (ha f g) u
  have he : ((rationalChainMap (topologicalProductMap f g)).f n).hom u = chainOfSimplex ℚ σ :=
    (universalProductSimplex_map X Y n σ₁ σ₂).trans
      (congrArg (chainOfSimplex ℚ) (pairedSimplex_projections X Y n σ))
  change ((rationalChainMap (topologicalProductMap f g)).f m).hom (a _ _ u) = _
  exact hn.symm.trans (congrArg (a X Y) he)

#print axioms productSelfModelExtension_boundary
end HodgeLean.Foundations.Singular
