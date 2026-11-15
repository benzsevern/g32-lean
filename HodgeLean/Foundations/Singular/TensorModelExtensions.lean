import HodgeLean.Foundations.Singular.ProductUniversalGenerators

/-! Natural maps from total tensor generators to chosen tensor-model chains. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- Extend tensor-model chains in an arbitrary target degree from actual simplex-pair generators.
Source: Hatcher, Algebraic Topology, §3.2, acyclic models for the Eilenberg–Zilber comparison. -/
def tensorModelExtension (X Y : TopCat.{0}) (n m : ℕ)
    (c : ∀ (p q : ℕ), p + q = n →
      (rationalTensorChains (TopCat.of (Convexity.StdSimplex ℝ (Fin (p + 1))))
        (TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1))))).X m) :
    (rationalTensorChains X Y).X n →ₗ[ℚ] (rationalTensorChains X Y).X m :=
  rationalTotalTensorLift X Y n (fun p q hpq σ τ =>
    ((rationalTensorChainMap (singularSimplexTopCatMap X p σ)
      (singularSimplexTopCatMap Y q τ)).f m).hom (c p q hpq))

/-- The tensor-model extension evaluates by the specified pushforward on each simplex-pair generator.
Source: Hatcher, Algebraic Topology, §3.2, acyclic models for the Eilenberg–Zilber comparison. -/
theorem tensorModelExtension_simplex (X Y : TopCat.{0}) (n m : ℕ)
    (c : ∀ (p q : ℕ), p + q = n →
      (rationalTensorChains (TopCat.of (Convexity.StdSimplex ℝ (Fin (p + 1))))
        (TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1))))).X m)
    (p q : ℕ) (hpq : p + q = n)
    (σ : (TopCat.toSSet.obj X) _⦋p⦌) (τ : (TopCat.toSSet.obj Y) _⦋q⦌) :
    tensorModelExtension X Y n m c
      ((tensorChainInclusion X Y p q n hpq).hom
        (chainOfSimplex ℚ σ ⊗ₜ[ℚ] chainOfSimplex ℚ τ)) =
      ((rationalTensorChainMap (singularSimplexTopCatMap X p σ)
        (singularSimplexTopCatMap Y q τ)).f m).hom (c p q hpq) :=
  rationalTotalTensorLift_simplex X Y n _ p q hpq σ τ

/-- Composing maps on both factors composes their actual tensor chain maps.
Source: Hatcher, Algebraic Topology, §3.2, functoriality of the tensor complex. -/
theorem rationalTensorChainMap_comp
    {X X' X'' Y Y' Y'' : TopCat.{0}}
    (f : X ⟶ X') (f' : X' ⟶ X'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    rationalTensorChainMap (f ≫ f') (g ≫ g') =
      rationalTensorChainMap f g ≫ rationalTensorChainMap f' g' := by
  let F := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  change HomologicalComplex.tensorHom (F.map (f ≫ f')) (F.map (g ≫ g')) =
    HomologicalComplex.tensorHom (F.map f) (F.map g) ≫
      HomologicalComplex.tensorHom (F.map f') (F.map g')
  rw [F.map_comp, F.map_comp]
  exact (MonoidalCategory.tensorHom_comp_tensorHom (F.map f) (F.map g) (F.map f') (F.map g')).symm

/-- Extension from tensor models is natural in both spaces, including shifted target degrees.
Source: Hatcher, Algebraic Topology, §3.2, acyclic models for the Eilenberg–Zilber comparison. -/
theorem tensorModelExtension_naturality
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') (n m : ℕ)
    (c : ∀ (p q : ℕ), p + q = n →
      (rationalTensorChains (TopCat.of (Convexity.StdSimplex ℝ (Fin (p + 1))))
        (TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1))))).X m) :
    (tensorModelExtension X' Y' n m c).comp ((rationalTensorChainMap f g).f n).hom =
      (((rationalTensorChainMap f g).f m).hom).comp (tensorModelExtension X Y n m c) := by
  apply rationalTotalTensor_linearMap_ext X Y n
  intro p q hpq σ τ
  erw [LinearMap.comp_apply, rationalTensorChainMap_simplex,
    tensorModelExtension_simplex, LinearMap.comp_apply, tensorModelExtension_simplex]
  rw [singularSimplexTopCatMap_map f, singularSimplexTopCatMap_map g]
  exact congrArg (fun k => (k.f m).hom (c p q hpq))
    (rationalTensorChainMap_comp (singularSimplexTopCatMap X p σ) f
      (singularSimplexTopCatMap Y q τ) g)

#print axioms tensorModelExtension_naturality
#print axioms rationalTensorChainMap_comp
#print axioms tensorModelExtension
#print axioms tensorModelExtension_simplex
end HodgeLean.Foundations.Singular
