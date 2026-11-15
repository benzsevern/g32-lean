import HodgeLean.Foundations.QuotientDuality.RetainedCycleAmbientCap

noncomputable section
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular TopologicalSpace Opposite
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual ambient cap action as a map of relative-chain presheaves. -/
def retainedChainPresheafAmbientCap (X : TopCat.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p) :
    singularChainPresheaf ℚ X (p + q) ⟶ singularChainPresheaf ℚ X q where
  app U := (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
    (retainedRelativeAmbientCapHom (TopPair.ofSubset (U.unop : Set X)ᶜ) p q φ)
  naturality U V f := by
    exact congrArg ((forget₂ (ModuleCat ℚ) AddCommGrpCat).map)
      (retained_relative_ambient_cap_support_inclusion X p q φ (leOfHom f.unop))

/-- Sheafification of the actual relative-chain presheaf cap action. -/
def retainedChainSheafAmbientCap (X : TopCat.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p) :
    singularChainSheaf ℚ X (p + q) ⟶ singularChainSheaf ℚ X q :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
    (retainedChainPresheafAmbientCap X p q φ)

/-- Sheafification retains the actual cap action on every original relative-chain section. -/
theorem retained_chain_sheaf_ambient_cap_unit (X : TopCat.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p) :
    toSheafify (Opens.grothendieckTopology X) (singularChainPresheaf ℚ X (p + q)) ≫
      (retainedChainSheafAmbientCap X p q φ).hom =
    retainedChainPresheafAmbientCap X p q φ ≫
      toSheafify (Opens.grothendieckTopology X) (singularChainPresheaf ℚ X q) :=
  (toSheafify_naturality (Opens.grothendieckTopology X)
    (retainedChainPresheafAmbientCap X p q φ)).symm

/-- The actual presheaf cap action satisfies the signed differential identity. -/
theorem retained_chain_presheaf_ambient_cap_boundary
    (X : TopCat.{0}) (p q : ℕ) (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0) :
    retainedChainPresheafAmbientCap X p (q + 1) φ ≫ singularChainBoundary ℚ X q =
      (-1 : ℤ) ^ p •
        (singularChainBoundary ℚ X (p + q) ≫ retainedChainPresheafAmbientCap X p q φ) := by
  apply NatTrans.ext
  funext U
  exact congrArg ((forget₂ (ModuleCat ℚ) AddCommGrpCat).map)
    (retained_relative_ambient_cap_boundary (TopPair.ofSubset (U.unop : Set X)ᶜ) p q φ hφ)

/-- Sheafification preserves the signed differential identity of the actual cap action. -/
theorem retained_chain_sheaf_ambient_cap_boundary
    (X : TopCat.{0}) (p q : ℕ) (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0) :
    retainedChainSheafAmbientCap X p (q + 1) φ ≫ singularChainSheafBoundary ℚ X q =
      (-1 : ℤ) ^ p •
        (singularChainSheafBoundary ℚ X (p + q) ≫ retainedChainSheafAmbientCap X p q φ) := by
  let F := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat
  have h := congrArg F.map (retained_chain_presheaf_ambient_cap_boundary X p q φ hφ)
  simpa only [F, Functor.map_comp, Functor.map_zsmul,
    retainedChainSheafAmbientCap, singularChainSheafBoundary] using h

end HodgeLean.Foundations.QuotientDuality
