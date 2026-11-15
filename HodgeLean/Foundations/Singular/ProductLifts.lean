import HodgeLean.Foundations.Singular.ProductGenerators

/-! Linear extension from the actual singular simplex generators. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- Extend prescribed simplex values to the actual rational singular chain group.
Source: Hatcher, Algebraic Topology, §2.1, freeness of singular chains. -/
def rationalChainLift
    (X : TopCat.{0}) (n : ℕ) {M : Type} [AddCommGroup M] [Module ℚ M]
    (f : (TopCat.toSSet.obj X) _⦋n⦌ → M) : (rationalChains X).X n →ₗ[ℚ] M :=
  (((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℚ ℚ) n).desc
    (Cofan.mk (ModuleCat.of ℚ M) (fun σ =>
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ M (f σ))))).hom

/-- The extension has its prescribed value on each actual unit simplex chain.
Source: Hatcher, Algebraic Topology, §2.1, the free singular chain group. -/
theorem rationalChainLift_simplex
    (X : TopCat.{0}) (n : ℕ) {M : Type} [AddCommGroup M] [Module ℚ M]
    (f : (TopCat.toSSet.obj X) _⦋n⦌ → M) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    rationalChainLift X n f (chainOfSimplex ℚ σ) = f σ := by
  let s := Cofan.mk (ModuleCat.of ℚ M) (fun σ =>
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ M (f σ)))
  have he := ((TopCat.toSSet.obj X).isColimitChainComplexXCofan
    (ModuleCat.of ℚ ℚ) n).fac s (Discrete.mk σ)
  have hv := congrArg (fun g => ModuleCat.Hom.hom g (1 : ℚ)) he
  change rationalChainLift X n f (chainOfSimplex ℚ σ) = (1 : ℚ) • f σ at hv
  simpa only [one_smul] using hv

/-- Extend prescribed values on simplex pairs to an actual tensor bidegree.
Source: Hatcher, Algebraic Topology, §3.2, the tensor universal property. -/
def rationalTensorLift
    (X Y : TopCat.{0}) (p q : ℕ) {M : Type} [AddCommGroup M] [Module ℚ M]
    (f : (TopCat.toSSet.obj X) _⦋p⦌ → (TopCat.toSSet.obj Y) _⦋q⦌ → M) :
    ((rationalChains X).X p ⊗[ℚ] (rationalChains Y).X q) →ₗ[ℚ] M :=
  TensorProduct.lift (rationalChainLift X p (fun σ => rationalChainLift Y q (f σ)))

/-- The tensor extension has its prescribed value on pairs of actual simplex chains.
Source: Hatcher, Algebraic Topology, §3.2, the tensor universal property. -/
theorem rationalTensorLift_simplex
    (X Y : TopCat.{0}) (p q : ℕ) {M : Type} [AddCommGroup M] [Module ℚ M]
    (f : (TopCat.toSSet.obj X) _⦋p⦌ → (TopCat.toSSet.obj Y) _⦋q⦌ → M)
    (σ : (TopCat.toSSet.obj X) _⦋p⦌) (τ : (TopCat.toSSet.obj Y) _⦋q⦌) :
    rationalTensorLift X Y p q f (chainOfSimplex ℚ σ ⊗ₜ[ℚ] chainOfSimplex ℚ τ) =
      f σ τ := by
  unfold rationalTensorLift
  erw [TensorProduct.lift.tmul, rationalChainLift_simplex, rationalChainLift_simplex]

/-- Extend compatible bidegree data to the actual total tensor chain group.
Source: Hatcher, Algebraic Topology, §3.2, the direct-sum universal property. -/
def rationalTotalTensorLift
    (X Y : TopCat.{0}) (n : ℕ) {M : Type} [AddCommGroup M] [Module ℚ M]
    (f : ∀ (p q : ℕ), p + q = n →
      (TopCat.toSSet.obj X) _⦋p⦌ → (TopCat.toSSet.obj Y) _⦋q⦌ → M) :
    (rationalTensorChains X Y).X n →ₗ[ℚ] M :=
  (HomologicalComplex.mapBifunctorDesc (K₁ := rationalChains X) (K₂ := rationalChains Y)
    (F := curriedTensor (ModuleCat ℚ)) (c := ComplexShape.down ℕ)
    (fun p q hpq => ModuleCat.ofHom (rationalTensorLift X Y p q (f p q hpq)))).hom

/-- The total extension has its prescribed value on each actual tensor simplex generator.
Source: Hatcher, Algebraic Topology, §3.2, the direct-sum universal property. -/
theorem rationalTotalTensorLift_simplex
    (X Y : TopCat.{0}) (n : ℕ) {M : Type} [AddCommGroup M] [Module ℚ M]
    (f : ∀ (p q : ℕ), p + q = n →
      (TopCat.toSSet.obj X) _⦋p⦌ → (TopCat.toSSet.obj Y) _⦋q⦌ → M)
    (p q : ℕ) (hpq : p + q = n)
    (σ : (TopCat.toSSet.obj X) _⦋p⦌) (τ : (TopCat.toSSet.obj Y) _⦋q⦌) :
    rationalTotalTensorLift X Y n f
      ((tensorChainInclusion X Y p q n hpq).hom
        (chainOfSimplex ℚ σ ⊗ₜ[ℚ] chainOfSimplex ℚ τ)) = f p q hpq σ τ := by
  have he := HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := rationalChains X) (K₂ := rationalChains Y)
    (F := curriedTensor (ModuleCat ℚ)) (c := ComplexShape.down ℕ)
    (fun p q hpq => ModuleCat.ofHom (rationalTensorLift X Y p q (f p q hpq))) p q hpq
  have hv := congrArg (fun g => ModuleCat.Hom.hom g
    (chainOfSimplex ℚ σ ⊗ₜ[ℚ] chainOfSimplex ℚ τ)) he
  change rationalTotalTensorLift X Y n f
      ((tensorChainInclusion X Y p q n hpq).hom
        (chainOfSimplex ℚ σ ⊗ₜ[ℚ] chainOfSimplex ℚ τ)) =
      rationalTensorLift X Y p q (f p q hpq)
        (chainOfSimplex ℚ σ ⊗ₜ[ℚ] chainOfSimplex ℚ τ) at hv
  exact hv.trans (rationalTensorLift_simplex X Y p q (f p q hpq) σ τ)

#print axioms rationalTotalTensorLift
#print axioms rationalTotalTensorLift_simplex
#print axioms rationalTensorLift
#print axioms rationalTensorLift_simplex
#print axioms rationalChainLift
#print axioms rationalChainLift_simplex
end HodgeLean.Foundations.Singular
