import HodgeLean.RealDefs.OrientationConstant
import Mathlib.Algebra.Module.Rat

/-! Actual morphisms of the constant rational sheaf are determined by constant unit sections.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Two endomorphisms of the actual constant rational sheaf agree if they agree on the constant unit section of every open set.
Source: Bredon, Sheaf Theory, second edition, I.1; rational additivity on constant stalks.
HC no distance; AV milestone no distance.
-/
theorem rationalConstantSheaf_hom_ext_one (X : TopCat.{0})
    (f g : TopCat.Sheaf.const X (AddCommGrpCat.of ℚ) ⟶ TopCat.Sheaf.const X (AddCommGrpCat.of ℚ))
    (h : ∀ U : Opens X, f.hom.app (op U) (constSection (AddCommGrpCat.of ℚ) U 1) =
      g.hom.app (op U) (constSection (AddCommGrpCat.of ℚ) U 1)) : f = g := by
  let A := AddCommGrpCat.of ℚ
  let P := TopCat.Presheaf.const X A
  let S := TopCat.Sheaf.const X A
  let J := Opens.grothendieckTopology X
  apply (sheafToPresheaf J AddCommGrpCat).map_injective
  apply sheafify_hom_ext J _ _ S.property
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro r
  change ℚ at r
  change f.hom.app U (constSection A U.unop r) = g.hom.app U (constSection A U.unop r)
  apply TopCat.Presheaf.section_ext S U.unop
  intro x hx
  let e := TopCat.Sheaf.constantSheafStalkIso A x
  apply (ConcreteCategory.bijective_of_isIso e.inv).1
  let bf : AddCommGrpCat.of ℚ ⟶ AddCommGrpCat.of ℚ := (toSheafify J P).app U ≫ f.hom.app U ≫ S.presheaf.germ U.unop x hx ≫ e.inv
  let bg : AddCommGrpCat.of ℚ ⟶ AddCommGrpCat.of ℚ := (toSheafify J P).app U ≫ g.hom.app U ≫ S.presheaf.germ U.unop x hx ≫ e.inv
  have h₁ : bf (1 : ℚ) = bg (1 : ℚ) :=
    congrArg (fun a => e.inv (S.presheaf.germ U.unop x hx a)) (h U.unop)
  change bf r = bg r
  calc
    bf r = bf (r • (1 : ℚ)) := by rw [smul_eq_mul, mul_one]
    _ = r • bf (1 : ℚ) := map_rat_smul bf.hom r 1
    _ = r • bg (1 : ℚ) := congrArg (r • ·) h₁
    _ = bg (r • (1 : ℚ)) := (map_rat_smul bg.hom r 1).symm
    _ = bg r := by rw [smul_eq_mul, mul_one]

#print axioms rationalConstantSheaf_hom_ext_one
end HodgeLean.Foundations.RationalHomologyManifold
