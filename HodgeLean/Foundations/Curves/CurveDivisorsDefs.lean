import HodgeLean.Foundations.Curves.CubicSmooth
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-! # Definitions for divisors on smooth projective curves (FROZEN)

These definitions reuse Mathlib's locally finite algebraic cycles, order of vanishing in the
function field, and degree of a zero-cycle.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace HodgeLean.Foundations.Curves

/-- Integral Weil divisors on a scheme, represented by Mathlib's locally finite cycles supported
in coheight one.
Source: Hartshorne, *Algebraic Geometry*, II.6; Mathlib
`AlgebraicGeometry.AlgebraicCycle.weilDivisors`. -/
abbrev Divisor (X : Scheme) := AlgebraicCycle.weilDivisors X ℤ

example (X : Scheme) : Divisor X = AlgebraicCycle.weilDivisors X ℤ := rfl

/-- The order of a nonzero rational function at a point of an integral locally Noetherian scheme.
Away from coheight one this is zero, exactly as in Mathlib's totalized `Scheme.ord`.
Source: Hartshorne, *Algebraic Geometry*, II.6; Mathlib `Scheme.ord`. -/
def ordAt (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X.functionField) (P : X) : ℤ := X.ord f P

example (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X.functionField) (P : X) : ordAt X f P = X.ord f P := rfl

/-- The principal divisor of a rational function. The fallback branch makes this an unconditional
definition; `ord_support_finite` in the frozen spec says that branch is never used on a smooth
projective curve for a nonzero function.
Source: Hartshorne, *Algebraic Geometry*, II.6, Proposition 6.5. -/
def principalDivisor (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X.functionField) : Divisor X := by
  classical
  by_cases hfin : (Function.support (ordAt X f)).Finite
  · refine ⟨Function.locallyFinsuppWithin.mk (ordAt X f) ?_ ?_, ?_⟩
    · exact fun _ _ ↦ Set.mem_univ _
    · intro z _
      exact ⟨Set.univ, Filter.univ_mem, by simpa using hfin⟩
    · intro x hx
      by_contra h
      exact hx (Scheme.ord_eq_zero_of_coheight_neq_one h f)
  · exact 0

example (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X.functionField) : AlgebraicCycle.IsWeilDivisor (principalDivisor X f).1 :=
  (principalDivisor X f).property

/-- Degree of a divisor on a compact curve over a base scheme, using residue-field degrees.
Source: Hartshorne, *Algebraic Geometry*, IV.1; Mathlib `AlgebraicCycle.degree`. -/
def divisorDegree {S : Scheme} (X : Over S) [CompactSpace X.left] : Divisor X.left →+ ℤ :=
  (AlgebraicCycle.degree X.hom).comp (AlgebraicCycle.weilDivisors X.left ℤ).subtype

example {S : Scheme} (X : Over S) [CompactSpace X.left] (D : Divisor X.left) :
    divisorDegree X D = AlgebraicCycle.degree X.hom D := rfl

/-- A scalar from the base field viewed as a rational function on a curve over `ℂ`.
Source: Hartshorne, *Algebraic Geometry*, II.3, the structure morphism on functions. -/
def constantFunction (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (c : ℂ) :
    X.left.functionField := by
  letI : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, trivial⟩⟩
  exact
  X.left.germToFunctionField ⊤
    (X.hom.appTop ((Scheme.ΓSpecIso ↧ℂ).inv c))

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (c : ℂ) :
    constantFunction X c = constantFunction X c := rfl

/-- The algebraic zero-cycle concentrated at one point with coefficient `n`.
Source: Mathlib `Function.locallyFinsuppWithin.single`. -/
def pointCycle (X : Scheme) (P : X) (n : ℤ) : AlgebraicCycle X ℤ := by
  classical
  exact Function.locallyFinsuppWithin.single P n

example (X : Scheme) (P : X) : pointCycle X P 0 = 0 := by
  classical
  ext Q
  simp [pointCycle]

/-- The rational function `x` on the fixed cubic, obtained from its Weierstrass affine chart.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.1. -/
def cubicX : E.left.functionField :=
  letI : Nonempty zChart := ⟨⟨finitePoint.base default, by
    have h := congrArg (fun U : (Spec ↧ℂ).Opens ↦ default ∈ U) finitePoint_zChart
    simpa using h⟩⟩
  E.left.germToFunctionField zChart
    (E.left.presheaf.map
      (eqToHom (by simp : zChart = zChart.ι ''ᵁ ⊤)).op
      ((zChart.ι.appIso ⊤).inv
        (zChartIso.hom.appTop
          ((Scheme.ΓSpecIso ↧W.toAffine.CoordinateRing).inv
            (AdjoinRoot.of W.toAffine.polynomial Polynomial.X)))))

/-- The cubic is locally Noetherian, being locally of finite type over `ℂ`.
Source: Hartshorne, *Algebraic Geometry*, II.3.2; Mathlib
`LocallyOfFiniteType.isLocallyNoetherian`. -/
noncomputable instance E_isLocallyNoetherian : IsLocallyNoetherian E.left :=
  LocallyOfFiniteType.isLocallyNoetherian E.hom

example : IsLocallyNoetherian E.left := inferInstance

/-- The cubic's underlying space is quasi-compact, since `E.hom` is quasi-compact over the
one-point space `Spec ℂ`. Source: Stacks Project, Tag 01K4; Mathlib
`QuasiCompact.compactSpace_of_compactSpace`. -/
noncomputable instance E_compactSpace : CompactSpace E.left :=
  QuasiCompact.compactSpace_of_compactSpace E.hom

example : CompactSpace E.left := inferInstance

end HodgeLean.Foundations.Curves
