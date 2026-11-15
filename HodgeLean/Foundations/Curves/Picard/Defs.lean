import HodgeLean.Foundations.Curves.CurveDivisorClasses

/-! # Pointed divisor classes of complex curves

The group objects are the existing Weil-divisor quotients. A point class is defined in the
full class group; the first-stage statements put it in the degree-zero subgroup at closed points.
No representing scheme or analytic torus is introduced here.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace HodgeLean.Foundations.Curves.Picard

/-- The additive group of degree-zero divisors, retaining the actual degree map.
Source: Hartshorne, Algebraic Geometry, II.6, Corollary 6.10. -/
abbrev DegreeZeroDivisors (X : Over (Spec ↧ℂ)) [CompactSpace X.left] :=
  (divisorDegree X).ker

example : pointDivisor E.left (finitePoint.base default) -
    pointDivisor E.left cubicInfinity ∈ DegreeZeroDivisors E := by
  change divisorDegree E _ = 0
  rw [map_sub, divisorDegree_pointDivisor _ finitePoint_isClosed,
    divisorDegree_pointDivisor _ cubicInfinity_isClosed, sub_self]

/-- Degree-zero divisor classes, using the existing image subgroup rather than a new quotient.
Source: Hartshorne, Algebraic Geometry, II.6, Example 6.10.2; `DivisorClassZero`. -/
abbrev DegreeZeroClasses (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [IsLocallyNoetherian X.left] [CompactSpace X.left] := DivisorClassZero X

example : cubicAbelMap (finitePoint.base default) ∈ DegreeZeroClasses E :=
  cubicAbelMap_mem_divisorClassZero _ finitePoint_isClosed

/-- The quotient homomorphism restricted to degree-zero divisors, with its image as codomain.
Source: Hartshorne, Algebraic Geometry, II.6, Example 6.10.2; `AddSubgroup.map`. -/
def classMap (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [IsLocallyNoetherian X.left] [CompactSpace X.left] :
    DegreeZeroDivisors X →+ DegreeZeroClasses X where
  toFun D := ⟨DivisorClass.mk X.left D, ⟨D, D.property, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' D F := Subtype.ext (map_add _ D.val F.val)

example (D F : DegreeZeroDivisors E) : classMap E (D - F) = classMap E D - classMap E F :=
  map_sub _ _ _

/-- The normalized point-class map with base point `Q`: the literal class of `[P] - [Q]`.
Its domain is the scheme's points; membership in degree zero requires closed points.
Source: Birkenhake–Lange, Complex Abelian Varieties, second edition, §11.4. -/
def pointClass (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [IsLocallyNoetherian X.left] (Q P : X.left) : DivisorClass X.left :=
  DivisorClass.mk X.left (pointDivisor X.left P - pointDivisor X.left Q)

example : pointClass E cubicInfinity (finitePoint.base default) ≠ 0 :=
  cubicAbelMap_finitePoint_ne_zero

end HodgeLean.Foundations.Curves.Picard
