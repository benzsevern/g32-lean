import HodgeLean.Adapters.CycleTranslateProofs

/-!
# Translation bookkeeping (FROZEN SPEC)

This specification covers steps 1–4 of the Kleiman route: inverse ideals under translation,
the single translated prime with coefficient one, preservation of coheight, preservation of the
prime component's cycle class. These are implications from the displayed geometric instances.
Generic existence, intersection coefficients, summation over cycles, and the final cup-product
packaging are outside this stage. HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Adapters

/-- The inverse ideal of a component under right translation is the prime ideal of its
translated generic point.
Source: Hartshorne, Algebraic Geometry, II.3 and II.5; Mathlib
`Scheme.IdealSheafData.comap`. -/
theorem hc9k_translate_inverseIdeal (X : Over (Spec ↧ℂ)) [GrpObj X]
    (t : ComplexPoint X) (y : X.left) :
    ccm3_inverseIdeal (GrpObj.mulRight t).hom.left y =
      ccm3_primeIdeal X.left (hc9k_translatePoint X t y) :=
  hc9k_translate_inverseIdeal_aux X t y

/-- The flat pullback of one prime component along right translation is the translated prime
with coefficient one.
Source: Fulton, Intersection Theory, second edition, §1.7; Kleiman,
Compositio Math. 28 (1974), §1. -/
theorem hc9k_translate_flatPullbackPrime (X : Over (Spec ↧ℂ)) [GrpObj X]
    [DecidableEq X.left] (t : ComplexPoint X) (y : X.left) :
    ccm3_flatPullbackPrime (GrpObj.mulRight t).hom.left y =
      Function.locallyFinsuppWithin.single (hc9k_translatePoint X t y) (1 : ℚ) :=
  hc9k_translate_flatPullbackPrime_aux X t y

/-- Right translation preserves the coheight of a component.
Source: Hartshorne, Algebraic Geometry, II.3; Mathlib `Order.coheight`. -/
theorem hc9k_translate_coheight (X : Over (Spec ↧ℂ)) [GrpObj X]
    (t : ComplexPoint X) (y : X.left) :
    Order.coheight (hc9k_translatePoint X t y) = Order.coheight y :=
  hc9k_translate_coheight_aux X t y

/-- The translated prime component has the cycle class of the original component.
Source: `ccm11_translated_cycleClass`, `ccm8_translation_pullback`, and Fulton,
Intersection Theory, second edition, §§1.7 and 19.1. -/
theorem hc9k_translate_cycleClass (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (t : ComplexPoint X) (q : ℕ) (y : X.left) (hy : Order.coheight y = q) :
    ccm3_cycleClass X q (ccm3_flatPullbackPrime (GrpObj.mulRight t).hom.left y) =
      cycleComponentSheafClass X y hy :=
  hc9k_translate_cycleClass_aux X t q y hy

open HodgeLean.Foundations HodgeLean.Foundations.Curves

local instance hc9k_decidableEqE : DecidableEq E.left := Classical.typeDecidableEq _

/-- Source: `ccm3_inverseIdeal` on the cubic group. -/
example := hc9k_translate_inverseIdeal E
  (Over.homMk finitePoint finitePoint_over : ComplexPoint E) cubicInfinity

/-- Source: `ccm3_flatPullbackPrime` on the cubic group. -/
example := hc9k_translate_flatPullbackPrime E
  (Over.homMk finitePoint finitePoint_over : ComplexPoint E) cubicInfinity

/-- Source: `coheight_eq_one_of_isClosed` on the cubic group. -/
example := hc9k_translate_coheight E
  (Over.homMk finitePoint finitePoint_over : ComplexPoint E) cubicInfinity

/-- Source: `cubicInfinity_isClosed` and `coheight_eq_one_of_isClosed`. -/
example := hc9k_translate_cycleClass E
  (Over.homMk finitePoint finitePoint_over : ComplexPoint E) 1 cubicInfinity
  (coheight_eq_one_of_isClosed E cubicInfinity cubicInfinity_isClosed)

end HodgeLean.Adapters
