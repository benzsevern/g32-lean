import HodgeLean.Foundations.Singular.ProductModels
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-! The total tensor complex of the actual rational singular chains. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory MonoidalCategory
namespace HodgeLean.Foundations.Singular

/-- The total tensor complex of the two actual rational singular chain complexes.
Source: Hatcher, Algebraic Topology, §3.2, the tensor chain complex. -/
abbrev rationalTensorChains (X Y : TopCat.{0}) : ChainComplex (ModuleCat ℚ) ℕ :=
  HomologicalComplex.tensorObj (rationalChains X) (rationalChains Y)

/-- The actual inclusion of a bidegree into total rational tensor chains.
Source: Hatcher, Algebraic Topology, §3.2, the total tensor chain complex. -/
abbrev tensorChainInclusion (X Y : TopCat.{0}) (p q n : ℕ) (hpq : p + q = n) :
    (rationalChains X).X p ⊗ (rationalChains Y).X q ⟶ (rationalTensorChains X Y).X n :=
  HomologicalComplex.ιTensorObj (rationalChains X) (rationalChains Y) p q n hpq

/-- The total differential on a tensor summand is the sum of its two component differentials.
Source: Hatcher, Algebraic Topology, §3.2, the tensor differential. -/
theorem tensorChainInclusion_boundary
    (X Y : TopCat.{0}) (p q n n' : ℕ) (hpq : p + q = n) :
    tensorChainInclusion X Y p q n hpq ≫ (rationalTensorChains X Y).d n n' =
      HomologicalComplex.mapBifunctor.d₁ (rationalChains X) (rationalChains Y)
        (curriedTensor (ModuleCat ℚ)) (ComplexShape.down ℕ) p q n' +
      HomologicalComplex.mapBifunctor.d₂ (rationalChains X) (rationalChains Y)
        (curriedTensor (ModuleCat ℚ)) (ComplexShape.down ℕ) p q n' := by
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]

/-- The total differential has the Koszul sign on the second factor.
Source: Hatcher, Algebraic Topology, §3.2, the tensor differential. -/
theorem tensorChainInclusion_boundary_succ_succ
    (X Y : TopCat.{0}) (p q : ℕ) :
    tensorChainInclusion X Y (p + 1) (q + 1) ((p + 1) + (q + 1)) rfl ≫
        (rationalTensorChains X Y).d ((p + 1) + (q + 1)) (p + q + 1) =
      ((rationalChains X).d (p + 1) p ▷ (rationalChains Y).X (q + 1)) ≫
        tensorChainInclusion X Y p (q + 1) (p + q + 1) (by omega) +
      ((-1 : ℤˣ) ^ (p + 1)) •
        (((rationalChains X).X (p + 1) ◁ (rationalChains Y).d (q + 1) q) ≫
          tensorChainInclusion X Y (p + 1) q (p + q + 1) (by omega)) := by
  rw [tensorChainInclusion_boundary,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.down ℕ).Rel (p + 1) p by simp)
      (q + 1) (p + q + 1) (by dsimp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ (p + 1)
      (show (ComplexShape.down ℕ).Rel (q + 1) q by simp) (p + q + 1) (by dsimp; omega)]
  change (1 : ℤˣ) • _ + ((-1 : ℤˣ) ^ (p + 1)) • _ = _
  simp only [one_smul]
  rfl

#print axioms tensorChainInclusion_boundary_succ_succ
#print axioms tensorChainInclusion_boundary
#print axioms rationalTensorChains
#print axioms tensorChainInclusion
end HodgeLean.Foundations.Singular
