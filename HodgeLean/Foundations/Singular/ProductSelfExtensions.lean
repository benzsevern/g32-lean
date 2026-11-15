import HodgeLean.Foundations.Singular.ProductSelfModels

/-! Natural degree-raising extensions from diagonal product simplex models. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- Extend a chosen chain on the diagonal product model to actual product chains.
Source: Hatcher, Algebraic Topology, §3.2, acyclic models for the Eilenberg–Zilber comparison. -/
def productSelfModelExtension (X Y : TopCat.{0}) (n m : ℕ)
    (c : (rationalChains (TopCat.of (simplexProductModel n n))).X m) :
    (rationalChains (TopCat.of (X × Y))).X n →ₗ[ℚ]
      (rationalChains (TopCat.of (X × Y))).X m :=
  rationalChainLift (TopCat.of (X × Y)) n (fun σ =>
    ((rationalChainMap (simplexPairMap X Y n n
      ((TopCat.toSSet.map (productFirst X Y)).app _ σ)
      ((TopCat.toSSet.map (productSecond X Y)).app _ σ))).f m).hom c)

/-- The diagonal-model extension has its specified pushforward value on each actual product simplex.
Source: Hatcher, Algebraic Topology, §3.2, acyclic models for the Eilenberg–Zilber comparison. -/
theorem productSelfModelExtension_simplex (X Y : TopCat.{0}) (n m : ℕ)
    (c : (rationalChains (TopCat.of (simplexProductModel n n))).X m)
    (σ : (TopCat.toSSet.obj (TopCat.of (X × Y))) _⦋n⦌) :
    productSelfModelExtension X Y n m c (chainOfSimplex ℚ σ) =
      ((rationalChainMap (simplexPairMap X Y n n
        ((TopCat.toSSet.map (productFirst X Y)).app _ σ)
        ((TopCat.toSSet.map (productSecond X Y)).app _ σ))).f m).hom c :=
  rationalChainLift_simplex _ _ _ _

/-- Extension from diagonal product models is natural, including shifted target degrees.
Source: Hatcher, Algebraic Topology, §3.2, acyclic models for chain homotopies. -/
theorem productSelfModelExtension_naturality
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') (n m : ℕ)
    (c : (rationalChains (TopCat.of (simplexProductModel n n))).X m) :
    (productSelfModelExtension X' Y' n m c).comp
        ((rationalChainMap (topologicalProductMap f g)).f n).hom =
      (((rationalChainMap (topologicalProductMap f g)).f m).hom).comp
        (productSelfModelExtension X Y n m c) := by
  apply rationalChain_linearMap_ext (TopCat.of (X × Y)) n
  intro σ
  erw [LinearMap.comp_apply, rationalChainMap_simplex,
    productSelfModelExtension_simplex, LinearMap.comp_apply, productSelfModelExtension_simplex]
  rw [(productSimplexProjections_naturality f g n σ).1,
    (productSimplexProjections_naturality f g n σ).2, simplexPairMap_naturality]
  exact rationalChainMap_comp_apply _ _ m c

#print axioms productSelfModelExtension_naturality
#print axioms productSelfModelExtension
#print axioms productSelfModelExtension_simplex
end HodgeLean.Foundations.Singular
