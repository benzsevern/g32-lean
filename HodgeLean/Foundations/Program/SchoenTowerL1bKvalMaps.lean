import HodgeLean.Foundations.Program.SchoenTowerL1bKummerBranchRestriction

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual stalk map into the retained covering field.
Source: Mathlib `Scheme.stalkFunctionFieldAlgebra`. -/
def s2v_l1b_kval_stalkMap {K : Type} [Field K] (X : Scheme.{0}) [IsIntegral X]
    (x : X) (κ : X.functionField ⟶ CommRingCat.of K) : X.presheaf.stalk x →+* K :=
  κ.hom.comp (algebraMap (X.presheaf.stalk x) X.functionField)

example {K : Type} [Field K] (X : Scheme.{0}) [IsIntegral X]
    (x : X) (κ : X.functionField ⟶ CommRingCat.of K) :
    Function.Injective (s2v_l1b_kval_stalkMap X x κ) :=
  κ.hom.injective.comp (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)

end HodgeLean.Foundations.Program
