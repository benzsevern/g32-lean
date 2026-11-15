import HodgeLean.Foundations.Singular.ProductChains
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.Cap.Simplicial

/-! Actual simplex generators for the rational tensor chain complex. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- A rational singular-chain linear map is determined on the unit simplex chains.
Source: Hatcher, Algebraic Topology, §2.1, the free singular chain group. -/
theorem rationalChain_linearMap_ext
    (X : TopCat.{0}) (n : ℕ) {M : Type} [AddCommGroup M] [Module ℚ M]
    (f g : (rationalChains X).X n →ₗ[ℚ] M)
    (h : ∀ σ : (TopCat.toSSet.obj X) _⦋n⦌,
      f (chainOfSimplex ℚ σ) = g (chainOfSimplex ℚ σ)) : f = g := by
  have he : ModuleCat.ofHom f = ModuleCat.ofHom g := by
    apply SSet.chainComplex_hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    exact h σ
  exact congrArg ModuleCat.Hom.hom he

/-- A map from a tensor bidegree is determined on pairs of actual simplex chains.
Source: Hatcher, Algebraic Topology, §3.2, tensor products of free chain groups. -/
theorem rationalTensor_linearMap_ext
    (X Y : TopCat.{0}) (p q : ℕ) {M : Type} [AddCommGroup M] [Module ℚ M]
    (f g : ((rationalChains X).X p ⊗[ℚ] (rationalChains Y).X q) →ₗ[ℚ] M)
    (h : ∀ (σ : (TopCat.toSSet.obj X) _⦋p⦌) (τ : (TopCat.toSSet.obj Y) _⦋q⦌),
      f (chainOfSimplex ℚ σ ⊗ₜ[ℚ] chainOfSimplex ℚ τ) =
        g (chainOfSimplex ℚ σ ⊗ₜ[ℚ] chainOfSimplex ℚ τ)) : f = g := by
  apply TensorProduct.ext
  apply rationalChain_linearMap_ext X p
  intro σ
  apply rationalChain_linearMap_ext Y q
  intro τ
  exact h σ τ

/-- The actual simplex-pair generators determine maps from each total tensor degree.
Source: Hatcher, Algebraic Topology, §3.2, the total tensor chain group. -/
theorem rationalTotalTensor_linearMap_ext
    (X Y : TopCat.{0}) (n : ℕ) {M : Type} [AddCommGroup M] [Module ℚ M]
    (f g : (rationalTensorChains X Y).X n →ₗ[ℚ] M)
    (h : ∀ (p q : ℕ) (hpq : p + q = n)
      (σ : (TopCat.toSSet.obj X) _⦋p⦌) (τ : (TopCat.toSSet.obj Y) _⦋q⦌),
      f ((tensorChainInclusion X Y p q n hpq).hom
        (chainOfSimplex ℚ σ ⊗ₜ[ℚ] chainOfSimplex ℚ τ)) =
      g ((tensorChainInclusion X Y p q n hpq).hom
        (chainOfSimplex ℚ σ ⊗ₜ[ℚ] chainOfSimplex ℚ τ))) : f = g := by
  have he : ModuleCat.ofHom f = ModuleCat.ofHom g := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    apply ModuleCat.hom_ext
    apply rationalTensor_linearMap_ext X Y p q
    intro σ τ
    exact h p q hpq σ τ
  exact congrArg ModuleCat.Hom.hom he

#print axioms rationalTotalTensor_linearMap_ext
#print axioms rationalTensor_linearMap_ext
#print axioms rationalChain_linearMap_ext
end HodgeLean.Foundations.Singular
