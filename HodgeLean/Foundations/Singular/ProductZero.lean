import HodgeLean.Foundations.Singular.ProductInduction

/-! The initial degrees of the actual tensor-to-product chain comparison. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- The degree-one rational singular boundary vanishes on a space with at most one point.
Source: Hatcher, Algebraic Topology, §2.1, the two endpoints of a singular edge. -/
theorem rationalChain_boundary_one_of_subsingleton
    (X : Type) [TopologicalSpace X] [Subsingleton X] :
    ((rationalChains (TopCat.of X)).d 1 0).hom = 0 := by
  apply rationalChain_linearMap_ext (TopCat.of X) 1
  intro σ
  have hf : (TopCat.toSSet.obj (TopCat.of X)).δ (0 : Fin 2) σ =
      (TopCat.toSSet.obj (TopCat.of X)).δ (1 : Fin 2) σ :=
    ((TopCat.of X).toSSetObjEquiv _).injective (Subsingleton.elim _ _)
  change boundary ℚ 0 (chainOfSimplex ℚ σ) = 0
  rw [boundary_chainOfSimplex, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
    neg_smul, hf, add_neg_cancel]

/-- Pair two actual singular simplices of the same degree into a simplex of the product space.
Source: Hatcher, Algebraic Topology, §3.2, products of singular simplices. -/
def pairedSimplex (X Y : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (τ : (TopCat.toSSet.obj Y) _⦋n⦌) :
    (TopCat.toSSet.obj (TopCat.of (X × Y))) _⦋n⦌ :=
  (TopCat.toSSetObjEquiv _ _).symm
    ((X.toSSetObjEquiv _ σ).prodMk (Y.toSSetObjEquiv _ τ))

/-- Pairing singular simplices commutes with the actual product map.
Source: Hatcher, Algebraic Topology, §3.2, naturality of products. -/
theorem pairedSimplex_naturality
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (τ : (TopCat.toSSet.obj Y) _⦋n⦌) :
    pairedSimplex X' Y' n ((TopCat.toSSet.map f).app _ σ) ((TopCat.toSSet.map g).app _ τ) =
      (TopCat.toSSet.map (topologicalProductMap f g)).app _ (pairedSimplex X Y n σ τ) := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  ext w <;> rfl

/-- The actual degree-zero tensor-to-product map pairs the two singular vertices.
Source: Hatcher, Algebraic Topology, §3.2, the degree-zero cross product. -/
def tensorProductZero (X Y : TopCat.{0}) :
    (rationalTensorChains X Y).X 0 →ₗ[ℚ] (rationalChains (TopCat.of (X × Y))).X 0 :=
  rationalTotalTensorLift X Y 0 (fun p q hpq σ τ => by
    have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst p
    subst q
    exact chainOfSimplex ℚ (pairedSimplex X Y 0 σ τ))

/-- The actual degree-zero cross product has the specified value on vertices.
Source: Hatcher, Algebraic Topology, §3.2, the degree-zero cross product. -/
theorem tensorProductZero_simplex (X Y : TopCat.{0})
    (σ : (TopCat.toSSet.obj X) _⦋0⦌) (τ : (TopCat.toSSet.obj Y) _⦋0⦌) :
    tensorProductZero X Y
      ((tensorChainInclusion X Y 0 0 0 rfl).hom
        (chainOfSimplex ℚ σ ⊗ₜ[ℚ] chainOfSimplex ℚ τ)) =
      chainOfSimplex ℚ (pairedSimplex X Y 0 σ τ) := by
  unfold tensorProductZero
  erw [rationalTotalTensorLift_simplex]

/-- The actual degree-zero tensor-to-product map is natural in both spaces.
Source: Hatcher, Algebraic Topology, §3.2, naturality of the cross product. -/
theorem tensorProductZero_naturality
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') :
    (tensorProductZero X' Y').comp ((rationalTensorChainMap f g).f 0).hom =
      (((rationalChainMap (topologicalProductMap f g)).f 0).hom).comp (tensorProductZero X Y) := by
  apply rationalTotalTensor_linearMap_ext X Y 0
  intro p q hpq σ τ
  have hp : p = 0 := by omega
  have hq : q = 0 := by omega
  subst p
  subst q
  erw [LinearMap.comp_apply, rationalTensorChainMap_simplex,
    tensorProductZero_simplex, LinearMap.comp_apply, tensorProductZero_simplex,
    rationalChainMap_simplex]
  rw [pairedSimplex_naturality]

/-- The degree-one total tensor boundary vanishes when both spaces have at most one point.
Source: Hatcher, Algebraic Topology, §3.2, the tensor differential. -/
theorem rationalTensorChain_boundary_one_of_subsingleton
    (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [Subsingleton X] [Subsingleton Y] :
    ((rationalTensorChains (TopCat.of X) (TopCat.of Y)).d 1 0).hom = 0 := by
  let K := rationalChains (TopCat.of X)
  let L := rationalChains (TopCat.of Y)
  have hX : K.d 1 0 = 0 := ModuleCat.hom_ext (rationalChain_boundary_one_of_subsingleton X)
  have hY : L.d 1 0 = 0 := ModuleCat.hom_ext (rationalChain_boundary_one_of_subsingleton Y)
  have hc : (rationalTensorChains (TopCat.of X) (TopCat.of Y)).d 1 0 = 0 := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change p + q = 1 at hpq
    simp only [comp_zero]
    change tensorChainInclusion (TopCat.of X) (TopCat.of Y) p q 1 hpq ≫
      (rationalTensorChains (TopCat.of X) (TopCat.of Y)).d 1 0 = 0
    by_cases hp : p = 0
    · subst p
      have hq : q = 1 := by omega
      subst q
      rw [tensorChainInclusion_boundary,
        HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ 0 1 0 (by simp),
        HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ 0
          (show (ComplexShape.down ℕ).Rel 1 0 by simp) 0 rfl]
      change 0 + _ • (((curriedTensor (ModuleCat ℚ)).obj (K.X 0)).map (L.d 1 0) ≫ _) = 0
      rw [hY, Functor.map_zero, zero_comp, smul_zero, zero_add]
    · have hp1 : p = 1 := by omega
      have hq : q = 0 := by omega
      subst p
      subst q
      rw [tensorChainInclusion_boundary,
        HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ 1 0 0 (by simp),
        HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
          (show (ComplexShape.down ℕ).Rel 1 0 by simp) 0 0 rfl]
      change _ • (((curriedTensor (ModuleCat ℚ)).map (K.d 1 0)).app (L.X 0) ≫ _) + 0 = 0
      rw [hX, Functor.map_zero, zero_app, zero_comp, smul_zero, add_zero]
  exact congrArg ModuleCat.Hom.hom hc

#print axioms rationalTensorChain_boundary_one_of_subsingleton
#print axioms tensorProductZero_naturality
#print axioms tensorProductZero
#print axioms tensorProductZero_simplex
#print axioms pairedSimplex
#print axioms pairedSimplex_naturality
#print axioms rationalChain_boundary_one_of_subsingleton
end HodgeLean.Foundations.Singular
