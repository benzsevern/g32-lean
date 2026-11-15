import HodgeLean.Foundations.Curves.CubicDedekind
import HodgeLean.Foundations.Curves.CubicDivisor
import HodgeLean.Foundations.Curves.CurveDegree
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.PointwiseDimension

/-! # Closed points and prime divisors on curves

Closed points of a smooth complex curve have coheight one, so their prime divisors are unit point
cycles of degree one. The points of Mathlib's Weierstrass group go to closed points of the cubic.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace HodgeLean.Foundations.Curves

/-- A closed point of a smooth complex curve has coheight one.
Source: Hartshorne, *Algebraic Geometry*, II, Exercise 3.20; HodgeConjecture
`SmoothOfRelativeDimension.height_add_coheight_eq_of_isClosed`. -/
theorem coheight_eq_one_of_isClosed (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] (P : X.left) (hP : IsClosed ({P} : Set X.left)) :
    Order.coheight P = 1 := by
  have h := SmoothOfRelativeDimension.height_add_coheight_eq_of_isClosed (f := X.hom) (d := 1) P hP
  have hmin : IsMin P := by
    intro y hy
    have hy' : y ∈ closure {P} := by
      rwa [← specializes_iff_mem_closure, ← Scheme.le_iff_specializes]
    rw [hP.closure_eq] at hy'
    exact (Set.mem_singleton_iff.mp hy').ge
  rw [Order.IsMin.height_eq_zero hmin, zero_add] at h
  exact_mod_cast h

/-- At a closed point of a smooth complex curve the prime divisor is the unit point cycle.
Source: Hartshorne, *Algebraic Geometry*, II.6. -/
theorem pointDivisor_eq_pointCycle (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] (P : X.left) (hP : IsClosed ({P} : Set X.left)) :
    (pointDivisor X.left P : AlgebraicCycle X.left ℤ) = pointCycle X.left P 1 := by
  have h1 := coheight_eq_one_of_isClosed X P hP
  classical
  simp only [pointDivisor, h1, dite_true, pointCycle]

open Classical in
/-- The coefficients of a prime divisor. -/
theorem pointDivisor_apply (X : Scheme) (P Q : X) :
    (pointDivisor X P : AlgebraicCycle X ℤ) Q =
      if Order.coheight P = 1 ∧ Q = P then 1 else 0 := by
  by_cases h : Order.coheight P = 1
  · simp only [pointDivisor, h, dite_true, true_and]
    change Function.locallyFinsuppWithin.single P 1 Q = _
    rw [Function.locallyFinsuppWithin.single_apply]
  · simp only [pointDivisor, h, dite_false, false_and, ite_false]
    rfl

/-- The image of a `ℂ`-point that is a section of the structure map is closed.
Source: Mathlib `AlgebraicGeometry.pointEquivClosedPoint`. -/
theorem isClosed_of_section (p : Spec ↧ℂ ⟶ E.left) (hp : p ≫ E.hom = 𝟙 _) :
    IsClosed ({p.base default} : Set E.left) := by
  have := ((pointEquivClosedPoint E.hom) ⟨p, hp⟩).2
  have hd : (default : Spec ↧ℂ) = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
  rw [hd]
  exact this

/-- Points of Mathlib's Weierstrass group go to closed points of `E`.
Source: Hartshorne, *Algebraic Geometry*, II.3 (rational points are closed). -/
theorem cubicPointOf_isClosed' (P : W.toAffine.Point) :
    IsClosed ({cubicPointOf P} : Set E.left) := by
  cases P with
  | zero => exact isClosed_of_section infinity infinity_over
  | some x y h =>
    apply isClosed_of_section
    rw [Category.assoc, zChartMap_over, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext c
    exact equationEval_algebraMap h.1 c

/-- The affine origin of Mathlib's group goes to `finitePoint`.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.1. -/
theorem cubicPointOf_origin' :
    cubicPointOf (.some 0 0 W_nonsingular_origin) = finitePoint.base default := by
  rw [← finitePoint_chart]
  change (Spec.map (CommRingCat.ofHom (equationEval W_nonsingular_origin.1)) ≫ zChartMap).base
    default = _
  have : equationEval W_nonsingular_origin.1 = finitePointCoordinates :=
    coordinateRing_ringHom_ext
      (fun c ↦ (equationEval_algebraMap _ c).trans
        (CubicDivisor.finitePointCoordinates_algebraMap c).symm)
      ((equationEval_x _).trans finitePointCoordinates_values.1.symm)
      ((equationEval_y _).trans finitePointCoordinates_values.2.symm)
  rw [this]

/-- The point at infinity is closed. -/
theorem cubicInfinity_isClosed : IsClosed ({cubicInfinity} : Set E.left) :=
  cubicPointOf_isClosed' 0

/-- The point `(0,0)` is closed. -/
theorem finitePoint_isClosed : IsClosed ({finitePoint.base default} : Set E.left) := by
  rw [← cubicPointOf_origin']
  exact cubicPointOf_isClosed' _

/-- The prime divisor of a closed point of `E` has degree one.
Source: Hartshorne, *Algebraic Geometry*, IV.1; Mathlib `AlgebraicCycle.degree_single`. -/
theorem divisorDegree_pointDivisor (P : E.left) (hP : IsClosed ({P} : Set E.left)) :
    divisorDegree E (pointDivisor E.left P) = 1 := by
  classical
  rw [divisorDegree, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
    pointDivisor_eq_pointCycle E P hP, pointCycle, AlgebraicCycle.degree_single,
    residueDegree_eq_one hP, one_smul]

end HodgeLean.Foundations.Curves
