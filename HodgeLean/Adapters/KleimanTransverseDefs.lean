import HodgeLean.Adapters.CycleTranslate
import HodgeLean.Foundations.Mathlib.GenericFlatSmooth

/-! # Action maps for translation transversality (FROZEN DEFINITIONS) -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory

namespace HodgeLean.Adapters

/-- The product of the two reduced component closures used in the difference construction.
Source: Kleiman, "The transversality of a general translate", Compositio Math. 28
(1974), proof of Theorem 2. -/
abbrev hc9k_actionSource (X : Over (Spec ↧ℂ)) (x y : X.left) :
    Over (Spec ↧ℂ) :=
  Over.mk (cycleComponentι X.left x ≫ X.hom) ⨯
    Over.mk (cycleComponentι X.left y ≫ X.hom)

/-- The difference map `(a,b) ↦ a⁻¹b` on two reduced component closures.
Source: Kleiman, "The transversality of a general translate", Compositio Math. 28
(1974), proof of Theorem 2. -/
def hc9k_actionMap (X : Over (Spec ↧ℂ)) [GrpObj X] (x y : X.left) :
    (hc9k_actionSource X x y).left ⟶ X.left :=
  (CartesianMonoidalCategory.lift
      (Limits.prod.fst ≫ Over.homMk (cycleComponentι X.left x) rfl ≫ GrpObj.inv)
      (Limits.prod.snd ≫ Over.homMk (cycleComponentι X.left y) rfl) ≫
    MonObj.mul : hc9k_actionSource X x y ⟶ X).left

example (X : Over (Spec ↧ℂ)) [GrpObj X] (x y : X.left) :
    (hc9k_actionSource X x y).left ⟶ X.left := hc9k_actionMap X x y

/-- The product of the regular loci of two component closures.
Source: Hartshorne, *Algebraic Geometry*, III.10; Kleiman, Compositio Math. 28
(1974), Theorem 2. -/
abbrev hc9k_regularActionSource (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x y : X.left) : Over (Spec ↧ℂ) :=
  Over.mk ((cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫
      cycleComponentι X.left x ≫ X.hom) ⨯
    Over.mk ((cycleComponentι X.left y ≫ X.hom).smoothLocus.ι ≫
      cycleComponentι X.left y ≫ X.hom)

/-- The difference map restricted to the product of the two regular loci.
Source: Hartshorne, *Algebraic Geometry*, III.10; Kleiman, Compositio Math. 28
(1974), Theorem 2. -/
def hc9k_regularActionMap (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x y : X.left) :
    (hc9k_regularActionSource X x y).left ⟶ X.left :=
  (CartesianMonoidalCategory.lift
      (Limits.prod.fst ≫ Over.homMk
        ((cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫
          cycleComponentι X.left x) rfl ≫ GrpObj.inv)
      (Limits.prod.snd ≫ Over.homMk
        ((cycleComponentι X.left y ≫ X.hom).smoothLocus.ι ≫
          cycleComponentι X.left y) rfl) ≫
    MonObj.mul : hc9k_regularActionSource X x y ⟶ X).left

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x y : X.left) :
    (hc9k_regularActionSource X x y).left ⟶ X.left := hc9k_regularActionMap X x y

end HodgeLean.Adapters
