import HodgeLean.Foundations.Singular.ProductModelMaps

/-! Natural extensions of actual chains chosen on the universal product models. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- Composition of actual continuous maps acts by composition on rational singular chains.
Source: Hatcher, Algebraic Topology, §2.1, functoriality of singular chains. -/
theorem rationalChainMap_comp_apply
    {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (z : (rationalChains X).X n) :
    ((rationalChainMap (f ≫ g)).f n).hom z =
      ((rationalChainMap g).f n).hom (((rationalChainMap f).f n).hom z) := by
  exact congrArg (fun k : rationalChains X ⟶ rationalChains Z => (k.f n).hom z)
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map_comp f g)

/-- Extend actual chains on the universal product models to arbitrary spaces in a fixed degree.
Source: Hatcher, Algebraic Topology, §3.2, the acyclic-models construction. -/
def productModelExtension (X Y : TopCat.{0}) (n : ℕ)
    (c : ∀ (p q : ℕ), p + q = n →
      (rationalChains (TopCat.of (simplexProductModel p q))).X n) :
    (rationalTensorChains X Y).X n →ₗ[ℚ] (rationalChains (TopCat.of (X × Y))).X n :=
  rationalTotalTensorLift X Y n (fun p q hpq σ τ =>
    ((rationalChainMap (simplexPairMap X Y p q σ τ)).f n).hom (c p q hpq))

/-- The model extension on each actual simplex-pair generator is the pushforward of its model chain.
Source: Hatcher, Algebraic Topology, §3.2, the acyclic-models construction. -/
theorem productModelExtension_simplex (X Y : TopCat.{0}) (n : ℕ)
    (c : ∀ (p q : ℕ), p + q = n →
      (rationalChains (TopCat.of (simplexProductModel p q))).X n)
    (p q : ℕ) (hpq : p + q = n)
    (σ : (TopCat.toSSet.obj X) _⦋p⦌) (τ : (TopCat.toSSet.obj Y) _⦋q⦌) :
    productModelExtension X Y n c
      ((tensorChainInclusion X Y p q n hpq).hom
        (chainOfSimplex ℚ σ ⊗ₜ[ℚ] chainOfSimplex ℚ τ)) =
      ((rationalChainMap (simplexPairMap X Y p q σ τ)).f n).hom (c p q hpq) :=
  rationalTotalTensorLift_simplex X Y n _ p q hpq σ τ

/-- Universal model extension is natural in both actual topological spaces.
Source: Hatcher, Algebraic Topology, §3.2, the acyclic-models construction. -/
theorem productModelExtension_naturality
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ)
    (c : ∀ (p q : ℕ), p + q = n →
      (rationalChains (TopCat.of (simplexProductModel p q))).X n) :
    (productModelExtension X' Y' n c).comp ((rationalTensorChainMap f g).f n).hom =
      (((rationalChainMap (topologicalProductMap f g)).f n).hom).comp
        (productModelExtension X Y n c) := by
  apply rationalTotalTensor_linearMap_ext X Y n
  intro p q hpq σ τ
  erw [LinearMap.comp_apply, rationalTensorChainMap_simplex,
    productModelExtension_simplex, LinearMap.comp_apply, productModelExtension_simplex]
  rw [simplexPairMap_naturality]
  exact rationalChainMap_comp_apply _ _ n (c p q hpq)

#print axioms productModelExtension_naturality
#print axioms productModelExtension
#print axioms productModelExtension_simplex
#print axioms rationalChainMap_comp_apply
end HodgeLean.Foundations.Singular
