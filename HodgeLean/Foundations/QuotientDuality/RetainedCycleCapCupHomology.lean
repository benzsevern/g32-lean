import HodgeLean.Foundations.QuotientDuality.RetainedCycleCapCup
import HodgeLean.Foundations.QuotientDuality.RetainedCycleCapHomologySheaf

noncomputable section
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual Alexander–Whitney cup cochain with its cocycle condition retained. -/
def retainedAmbientCupCocycle (X : TopCat.{0}) (p q : ℕ)
    (φ : Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) p)
    (ψ : Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) q) :
    Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) (p + q) :=
  ⟨HodgeLean.Foundations.Singular.cupCochain X p q φ.1 ψ.1, by
    change Simplicial.coboundary ℚ (p + q)
      (HodgeLean.Foundations.Singular.cupCochain X p q φ.1 ψ.1) = 0
    rw [HodgeLean.Foundations.Singular.coboundary_cupCochain, φ.2, ψ.2]
    simp⟩

/-- The actual cup cocycle represents the actual singular cup product. -/
theorem retained_cup_cocycle_class (X : TopCat.{0}) (p q : ℕ)
    (φ : Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) p)
    (ψ : Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) q) :
    HodgeLean.Foundations.Singular.cup X rfl
      (HodgeLean.Foundations.Singular.cohomologyClass X p φ)
      (HodgeLean.Foundations.Singular.cohomologyClass X q ψ) =
    HodgeLean.Foundations.Singular.cohomologyClass X (p + q) (retainedAmbientCupCocycle X p q φ ψ) := by
  unfold HodgeLean.Foundations.Singular.cup HodgeLean.Foundations.Singular.cohomologyClass
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rfl

/-- Cup-cap composition holds for the induced maps on actual relative homology. -/
theorem retained_relative_cap_cup_homology (P : TopPair.{0}) (p q r : ℕ)
    (φ : Simplicial.Cocycle ℚ (TopCat.toSSet.obj P.fst) p)
    (ψ : Simplicial.Cocycle ℚ (TopCat.toSSet.obj P.fst) q) :
    let K := (relativeChainFunctor ℚ).obj P
    let θ := retainedAmbientCupCocycle P.fst p q φ ψ
    ShortComplex.homologyMap (retainedRelativeCapShortComplex P (p + q) r θ.1 θ.2) =
      ShortComplex.homologyMap (eqToIso (congrArg K.sc (Nat.add_assoc p q r))).hom ≫
        ShortComplex.homologyMap (retainedRelativeCapShortComplex P p (q + r) φ.1 φ.2) ≫
        ShortComplex.homologyMap (retainedRelativeCapShortComplex P q r ψ.1 ψ.2) := by
  dsimp only
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  apply retained_homology_map_eq_of_middle
  simp only [ShortComplex.comp_τ₂, retained_relative_cap_short_complex_middle]
  have he (a b : ℕ) (hab : a = b) :
      (eqToIso (congrArg ((relativeChainFunctor ℚ).obj P).sc hab)).hom.τ₂ =
        (((relativeChainFunctor ℚ).obj P).XIsoOfEq hab).hom := by
    subst b
    rfl
  rw [he]
  exact retained_relative_chain_cap_cup P p q r φ.1 ψ.1

/-- Cup-cap composition holds on the actual chain-homology sheaves. -/
theorem retained_chain_homology_sheaf_cap_cup (X : TopCat.{0}) (p q r : ℕ)
    (φ : Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) p)
    (ψ : Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) q) :
    let K := singularChainSheafComplex ℚ X
    let θ := retainedAmbientCupCocycle X p q φ ψ
    retainedChainSheafCapHomology X (p + q) r θ.1 θ.2 =
      ShortComplex.homologyMap (eqToIso (congrArg K.sc (Nat.add_assoc p q r))).hom ≫
        retainedChainSheafCapHomology X p (q + r) φ.1 φ.2 ≫
        retainedChainSheafCapHomology X q r ψ.1 ψ.2 := by
  dsimp only
  unfold retainedChainSheafCapHomology
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  apply retained_homology_map_eq_of_middle
  simp only [ShortComplex.comp_τ₂, retained_chain_sheaf_cap_short_complex_middle]
  have he (a b : ℕ) (hab : a = b) :
      (eqToIso (congrArg (singularChainSheafComplex ℚ X).sc hab)).hom.τ₂ =
        ((singularChainSheafComplex ℚ X).XIsoOfEq hab).hom := by
    subst b
    rfl
  rw [he]
  exact retained_chain_sheaf_cap_cup X p q r φ.1 ψ.1

end HodgeLean.Foundations.QuotientDuality
