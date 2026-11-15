import HodgeLean.Adapters.LefschetzOneOneHodgeAbelian2
import HodgeLean.Adapters.CycleClassPullbackSpan
import HodgeLean.Foundations.Curves.CurveCycleClass
import HodgeLean.Foundations.SegreProjective
import HodgeLean.Foundations.GeometricIntegralityC

/-! # The even algebraic submodules

A restricted interface retaining linear closure without asserting product closure.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.Curves
namespace HodgeLean.Adapters

/-- Pull the actual cycle span back to the even exterior power. This constructor
supplies linear closure only; powers of a chosen divisor remain separate inputs.
Source: `RealDefs.isAlgebraicOf_iff` and `Submodule.comap`. -/
def ccm8_cycleClassSubmodule (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (μ : CupProduct X) (p : ℕ) : Submodule ℚ (⋀[ℚ]^(2 * p) (HQ X 1)) :=
  (algebraicCycleClassSpan X p).comap (μ.cupWedgeMap (2 * p))

/-- Source: linear closure of the constructed submodule. -/
example : (0 : ⋀[ℚ]^(2 * 1) (HQ E 1)) ∈
    ccm8_cycleClassSubmodule E (cupProductOf E) 1 := Submodule.zero_mem _

/-- The point-divisor class on the cubic.
Source: `divisorCycleClass` in `CurveCycleClassDefs.lean` and the cubic point at infinity. -/
def ccm8_pointClass : HQ E 2 :=
  divisorCycleClass E (pointDivisor E.left cubicInfinity)

/-- Source: the nonvanishing theorem for a closed point of a curve. -/
example : ccm8_pointClass ≠ 0 :=
  divisorCycleClass_pointDivisor_ne_zero E cubicInfinity cubicInfinity_isClosed

/-- Source: geometric integrality of the cubic self-product. -/
instance ccm8_commE : IsCommMonObj E :=
  isCommMonObj_of_complexSelfProductIntegral E (complexSelfProductIntegral_of_isIntegral E)

/-- The theta-product class on the iterated square: the sum of the two
pullbacks of the point divisor. No intersection comparison is part of this definition.
Source: Birkenhake--Lange, Complex Abelian Varieties, second edition, chapter 3;
the product class is constructed here by pullback and addition. -/
def ccm8_thetaClass : HQ (g3_power E 2) 2 :=
  homPullback ((g3_powerData E 2).proj 0) 2 ccm8_pointClass +
    homPullback ((g3_powerData E 2).proj 1) 2 ccm8_pointClass

/-- Source: the definition of the product polarization class. -/
example : ccm8_thetaClass =
    homPullback ((g3_powerData E 2).proj 0) 2 ccm8_pointClass +
      homPullback ((g3_powerData E 2).proj 1) 2 ccm8_pointClass := rfl

/-- The nonzero cubic divisor lifts into the restricted algebraic submodule.
Source: the cubic degree-two span and the torus comparison. -/
example : ((torusCohomology_cupProductOf E).cupWedgeEquiv 2).symm ccm8_pointClass ∈
    ccm8_cycleClassSubmodule E (cupProductOf E) 1 := by
  change (cupProductOf E).cupWedgeMap 2 _ ∈ algebraicCycleClassSpan E 1
  rw [algebraicCycleClassSpan_one_cubic]
  trivial

end HodgeLean.Adapters
