import HodgeLean.Foundations.Singular.ProductLifts

/-! Naturality on actual singular and tensor simplex generators. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- The actual rational singular chain map of a continuous map.
Source: Hatcher, Algebraic Topology, §2.1, functoriality of singular chains. -/
abbrev rationalChainMap {X Y : TopCat.{0}} (f : X ⟶ Y) :
    rationalChains X ⟶ rationalChains Y :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map f

/-- The actual chain map sends a unit simplex chain to the image simplex chain.
Source: Hatcher, Algebraic Topology, §2.1, functoriality of singular chains. -/
theorem rationalChainMap_simplex {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    ((rationalChainMap f).f n).hom (chainOfSimplex ℚ σ) =
      chainOfSimplex ℚ ((TopCat.toSSet.map f).app _ σ) :=
  chainOfSimplex_map ℚ (TopCat.toSSet.map f) σ

/-- Linear extension commutes with actual continuous-map pullback on simplex data.
Source: Hatcher, Algebraic Topology, §2.1, naturality of free singular chains. -/
theorem rationalChainLift_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    {M : Type} [AddCommGroup M] [Module ℚ M]
    (a : (TopCat.toSSet.obj Y) _⦋n⦌ → M) :
    (rationalChainLift Y n a).comp ((rationalChainMap f).f n).hom =
      rationalChainLift X n (fun σ => a ((TopCat.toSSet.map f).app _ σ)) := by
  apply rationalChain_linearMap_ext X n
  intro σ
  erw [LinearMap.comp_apply, rationalChainMap_simplex,
    rationalChainLift_simplex, rationalChainLift_simplex]

/-- The actual tensor-complex map of two continuous maps.
Source: Hatcher, Algebraic Topology, §3.2, functoriality of tensor chain complexes. -/
abbrev rationalTensorChainMap {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') :
    rationalTensorChains X Y ⟶ rationalTensorChains X' Y' :=
  HomologicalComplex.tensorHom (rationalChainMap f) (rationalChainMap g)

/-- Bidegree inclusions intertwine the actual tensor-complex map with its two factor maps.
Source: Hatcher, Algebraic Topology, §3.2, functoriality of the tensor chain complex. -/
theorem tensorChainInclusion_naturality
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y')
    (p q n : ℕ) (hpq : p + q = n) :
    tensorChainInclusion X Y p q n hpq ≫ (rationalTensorChainMap f g).f n =
      ((rationalChainMap f).f p ⊗ₘ (rationalChainMap g).f q) ≫
        tensorChainInclusion X' Y' p q n hpq := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc]
  exact HomologicalComplex.ι_mapBifunctorMap (rationalChainMap f) (rationalChainMap g)
    (curriedTensor (ModuleCat ℚ)) (ComplexShape.down ℕ) p q n hpq

/-- The actual total tensor chain map has the expected value on simplex-pair generators.
Source: Hatcher, Algebraic Topology, §3.2, functoriality of tensor chain complexes. -/
theorem rationalTensorChainMap_simplex
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y')
    (p q n : ℕ) (hpq : p + q = n)
    (σ : (TopCat.toSSet.obj X) _⦋p⦌) (τ : (TopCat.toSSet.obj Y) _⦋q⦌) :
    ((rationalTensorChainMap f g).f n).hom
      ((tensorChainInclusion X Y p q n hpq).hom
        (chainOfSimplex ℚ σ ⊗ₜ[ℚ] chainOfSimplex ℚ τ)) =
      (tensorChainInclusion X' Y' p q n hpq).hom
        (chainOfSimplex ℚ ((TopCat.toSSet.map f).app _ σ) ⊗ₜ[ℚ]
          chainOfSimplex ℚ ((TopCat.toSSet.map g).app _ τ)) := by
  have he := tensorChainInclusion_naturality f g p q n hpq
  have hv := congrArg (fun k => ModuleCat.Hom.hom k
    (chainOfSimplex ℚ σ ⊗ₜ[ℚ] chainOfSimplex ℚ τ)) he
  change ((rationalTensorChainMap f g).f n).hom
      ((tensorChainInclusion X Y p q n hpq).hom
        (chainOfSimplex ℚ σ ⊗ₜ[ℚ] chainOfSimplex ℚ τ)) =
      (tensorChainInclusion X' Y' p q n hpq).hom
        (((rationalChainMap f).f p ⊗ₘ (rationalChainMap g).f q).hom
          (chainOfSimplex ℚ σ ⊗ₜ[ℚ] chainOfSimplex ℚ τ)) at hv
  erw [ModuleCat.MonoidalCategory.tensorHom_tmul,
    rationalChainMap_simplex, rationalChainMap_simplex] at hv
  exact hv

#print axioms rationalTensorChainMap_simplex
#print axioms rationalTensorChainMap
#print axioms tensorChainInclusion_naturality
#print axioms rationalChainLift_naturality
#print axioms rationalChainMap
#print axioms rationalChainMap_simplex
end HodgeLean.Foundations.Singular
