import HodgeLean.Foundations.Curves.CurveCycleClassProofs

/-! # The divisor cycle-class map on curves (FROZEN SPEC)

This file freezes the J5 interface (`docs/roadmap/curves.md` §J5, `docs/specs/CurveCycleClass.md`)
between Weil divisors and upstream's cycle classes in `HQ X 2 = H²(X(ℂ); ℚ)`. Each theorem is
proved by the matching `_aux` theorem in `CurveCycleClassProofs.lean`.

**Claimed.**
* On an integral smooth projective `X` over `ℂ`, the divisor cycle-class map
  `divisorCycleClass X : Divisor X.left →+ HQ X 2` agrees on prime divisors with upstream's
  `cycleComponentSheafClass`.
* On an integral smooth projective curve, the class of a closed point is nonzero, and when
  `finrank ℚ (HQ X 2) = 1` it spans `HQ X 2` and `algebraicCycleClassSpan X 1 = ⊤`. On the cubic
  `E`, where that rank is the proved `finrank_HQ_cubic`, `algebraicCycleClassSpan E 1 = ⊤`.
* As an implication from `ComplexPointsPreconnected`: on a curve the class of a divisor is its
  degree times the class of a closed point, so principal divisors have class zero and the map
  descends to `DivisorClass X.left`; on `E`, `[(0,0)]` and `[∞]` have the same class in `HQ E 2`
  although they differ in `Cl(E)`.

**Not claimed.** No rational-equivalence invariance in dimension above one, no first Chern class
or line bundle, no Poincaré duality or degree map on `HQ X 2`, no injectivity statement for the
descended map on `Cl⁰`, no computation of `finrank ℚ (HQ X 2)` for curves other than `E`, and no
Hodge-theoretic input. The span statement on `E` is the codimension-one Hodge statement on `E`
only through `le_top`; it is not the universal `LefschetzOneOneHyp`.
Relation to the goal: HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs

namespace HodgeLean.Foundations.Curves

/-- **Agreement on prime divisors.** The divisor cycle class of the prime divisor with generic
point `P` is upstream's cycle class of the closure of `P`.
Source: Fulton, *Intersection Theory*, 2nd ed., §19.1; HodgeConjecture
`AlgebraicGeometry.ComplexPoint.cycleComponentSheafClass`. -/
theorem divisorCycleClass_pointDivisor (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] [CompactSpace X.left] (P : X.left)
    (hP : Order.coheight P = ((1 : ℕ) : ℕ∞)) :
    divisorCycleClass X (pointDivisor X.left P) = cycleComponentSheafClass X P hP :=
  divisorCycleClass_pointDivisor_aux X P hP

example (P : E.left) (hP : IsClosed ({P} : Set E.left)) :
    divisorCycleClass E (pointDivisor E.left P) =
      cycleComponentSheafClass E P ((coheight_eq_one_of_isClosed E P hP).trans
        Nat.cast_one.symm) :=
  divisorCycleClass_pointDivisor E P _

/-- **The point class is nonzero.** On a smooth projective curve the class of a closed point is a
nonzero element of `H²(X(ℂ); ℚ)`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0, §4 (the fundamental class of
a point of a compact Riemann surface is the orientation class); Fulton, *Intersection Theory*,
2nd ed., Example 19.1.11. -/
theorem divisorCycleClass_pointDivisor_ne_zero (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    [CompactSpace X.left] (P : X.left) (hP : IsClosed ({P} : Set X.left)) :
    divisorCycleClass X (pointDivisor X.left P) ≠ 0 :=
  divisorCycleClass_pointDivisor_ne_zero_aux X P hP

example : divisorCycleClass E (pointDivisor E.left cubicInfinity) ≠ 0 :=
  divisorCycleClass_pointDivisor_ne_zero E _ cubicInfinity_isClosed

/-- **Degree from class**, as an implication from `ComplexPointsPreconnected`. On a curve, the
class of a divisor is its degree times the class of any closed point.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0, §4 and Ch. 2, §1
(`η_D = deg D · ω` on a compact Riemann surface); Fulton, *Intersection Theory*, 2nd ed.,
Example 19.1.11. -/
theorem divisorCycleClass_eq_degree_smul (hconn : ComplexPointsPreconnected)
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProjective X.hom] [CompactSpace X.left] (D : Divisor X.left) (P : X.left)
    (hP : IsClosed ({P} : Set X.left)) :
    divisorCycleClass X D = divisorDegree X D • divisorCycleClass X (pointDivisor X.left P) :=
  divisorCycleClass_eq_degree_smul_aux hconn X D P hP

example (hconn : ComplexPointsPreconnected) (P : E.left) (hP : IsClosed ({P} : Set E.left)) :
    divisorCycleClass E (pointDivisor E.left P) =
      divisorCycleClass E (pointDivisor E.left cubicInfinity) := by
  rw [divisorCycleClass_eq_degree_smul hconn E _ cubicInfinity cubicInfinity_isClosed,
    divisorDegree_pointDivisor P hP, one_smul]

/-- **Vanishing on principal divisors**, as an implication from `ComplexPointsPreconnected`: the
rational-equivalence step for curves, so the map descends through `divisorClassCycleClass`.
Source: Fulton, *Intersection Theory*, 2nd ed., Corollary 19.2; Hartshorne, *Algebraic Geometry*,
II.6, Corollary 6.10 (principal divisors have degree zero). -/
theorem principalDivisors_le_ker_divisorCycleClass (hconn : ComplexPointsPreconnected)
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProjective X.hom] [IsLocallyNoetherian X.left] [CompactSpace X.left] :
    principalDivisors X.left ≤ (divisorCycleClass X).ker :=
  principalDivisors_le_ker_divisorCycleClass_aux hconn X

example (hconn : ComplexPointsPreconnected) : DivisorClass E.left →+ HQ E 2 :=
  divisorClassCycleClass E (principalDivisors_le_ker_divisorCycleClass hconn E)

/-- **The point class generates `H²`.** If `H²(X(ℂ); ℚ)` of a curve is a line, the class of any
closed point spans it.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0, §4; with
`span_singleton_eq_top_of_rank_le_one` (`RealDefs/DegreeZero.lean`). -/
theorem span_divisorCycleClass_pointDivisor (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    [CompactSpace X.left] (h : Module.finrank ℚ (HQ X 2) = 1) (P : X.left)
    (hP : IsClosed ({P} : Set X.left)) :
    Submodule.span ℚ {divisorCycleClass X (pointDivisor X.left P)} = ⊤ :=
  span_divisorCycleClass_pointDivisor_aux X h P hP

example (P : E.left) (hP : IsClosed ({P} : Set E.left)) :
    Submodule.span ℚ {divisorCycleClass E (pointDivisor E.left P)} = ⊤ :=
  span_divisorCycleClass_pointDivisor E (by rw [finrank_HQ_cubic]; rfl) P hP

/-- **The curve span statement.** If `H²(X(ℂ); ℚ)` of a curve is a line, the codimension-one
cycle classes span it. This is an implication from the nonvanishing and generation statements
above, at any closed point.
Source: `docs/roadmap/curves.md` §J5; Griffiths–Harris, *Principles of Algebraic Geometry*,
Ch. 0, §4; HodgeConjecture `AlgebraicGeometry.ComplexPoint.algebraicCycleClassSpan`. -/
theorem algebraicCycleClassSpan_one_eq_top (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (h : Module.finrank ℚ (HQ X 2) = 1) :
    algebraicCycleClassSpan X 1 = ⊤ :=
  algebraicCycleClassSpan_one_eq_top_aux X h

example : algebraicCycleClassSpan E 1 = ⊤ :=
  algebraicCycleClassSpan_one_eq_top E (by rw [finrank_HQ_cubic]; rfl)

/-- **The curve instance on `E`.** The codimension-one cycle classes of the cubic span
`H²(E(ℂ); ℚ)`; this is `algebraicCycleClassSpan_one_eq_top` at `E` with `finrank_HQ_cubic`.
Source: `finrank_HQ_cubic` (`CubicS13.lean`); Griffiths–Harris, *Principles of Algebraic
Geometry*, Ch. 0, §4. -/
theorem algebraicCycleClassSpan_one_cubic : algebraicCycleClassSpan E 1 = ⊤ :=
  algebraicCycleClassSpan_one_cubic_aux

/-- The codimension-one Hodge statement on `E` follows, through `le_top`. -/
example : Hdg^1(E; ℚ) ≤ algebraicCycleClassSpan E 1 := by
  rw [algebraicCycleClassSpan_one_cubic]
  exact le_top

/-- **Falsification**, as an implication from `ComplexPointsPreconnected`: `[(0,0)]` and `[∞]`
have the same class in `H²(E(ℂ); ℚ)`. They differ in `Cl(E)` (the J2 witness
`cubicAbelMap_finitePoint_ne_zero`), so `HQ E 2` sees the degree and not the class group.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.3.4 (`Cl⁰(E) ≅ E`); Griffiths–Harris,
*Principles of Algebraic Geometry*, Ch. 0, §4. -/
theorem divisorCycleClass_finitePoint_eq_infinity (hconn : ComplexPointsPreconnected) :
    divisorCycleClass E (pointDivisor E.left (finitePoint.base default)) =
      divisorCycleClass E (pointDivisor E.left cubicInfinity) :=
  divisorCycleClass_finitePoint_eq_infinity_aux hconn

example :
    DivisorClass.mk E.left (pointDivisor E.left (finitePoint.base default)) ≠
      DivisorClass.mk E.left (pointDivisor E.left cubicInfinity) := by
  intro h
  apply cubicAbelMap_finitePoint_ne_zero
  rw [cubicAbelMap, map_sub, h, sub_self]

end HodgeLean.Foundations.Curves
