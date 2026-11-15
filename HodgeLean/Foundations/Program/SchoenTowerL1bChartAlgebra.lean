import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChart
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

namespace HodgeLean.Foundations.Program
open Polynomial

/-- The affine ring for the chart with relation `u = X * v`. -/
abbrev s2v_L1bChart {R : Type*} [CommRing R] (u v : R) :=
  AlgebraicGeometry.RegularPairChart.ring u v

example {R : Type*} [CommRing R] (u v : R) :
    s2v_L1bChart u v = (R[X] ⧸ Ideal.span {C u - X * C v}) := rfl

/-- Polynomial evaluation at the chart parameter is the quotient map. -/
theorem s2v_l1b_chart_eval_eq_mk {R : Type*} [CommRing R] (u v : R) :
    eval₂RingHom ((Ideal.Quotient.mk (Ideal.span {C u - X * C v})).comp C)
      (Ideal.Quotient.mk (Ideal.span {C u - X * C v}) X) =
      Ideal.Quotient.mk (Ideal.span {C u - X * C v}) := by
  apply Polynomial.ringHom_ext'
  · ext r
    exact eval₂_C _ _
  · exact eval₂_X _ _

/-- The chart evaluation is onto and has exactly the binomial relation as its kernel. -/
theorem s2v_l1b_chart_presentation {R : Type*} [CommRing R] (u v : R) :
    Function.Surjective (eval₂RingHom
      ((Ideal.Quotient.mk (Ideal.span {C u - X * C v})).comp C)
      (Ideal.Quotient.mk (Ideal.span {C u - X * C v}) X)) ∧
    RingHom.ker (eval₂RingHom
      ((Ideal.Quotient.mk (Ideal.span {C u - X * C v})).comp C)
      (Ideal.Quotient.mk (Ideal.span {C u - X * C v}) X)) =
      Ideal.span {C u - X * C v} := by
  rw [s2v_l1b_chart_eval_eq_mk]
  exact ⟨Ideal.Quotient.mk_surjective, Ideal.mk_ker⟩

/-- The two base generators satisfy the chart equation in the quotient ring. -/
theorem s2v_l1b_chart_relation {R : Type*} [CommRing R] (u v : R) :
    let q := Ideal.Quotient.mk (Ideal.span {C u - X * C v})
    q (C u) = q X * q (C v) := by
  exact AlgebraicGeometry.RegularPairChart.chart_relation u v

/-- The selected ideal becomes principal on the algebraic chart. -/
theorem s2v_l1b_chart_centre_principal {R : Type*} [CommRing R] (u v : R) :
    let q := Ideal.Quotient.mk (Ideal.span {C u - X * C v})
    Ideal.span {q (C u), q (C v)} = Ideal.span {q (C v)} := by
  exact AlgebraicGeometry.RegularPairChart.centre_principal u v

/-- A solution of the chart equation induces a unique map from the chart ring. -/
theorem s2v_l1b_chart_lift {R A : Type*} [CommRing R] [CommRing A]
    (u v : R) (f : R →+* A) (s : A) (hs : f u = s * f v) :
    ∃! φ : s2v_L1bChart u v →+* A,
      φ.comp (Ideal.Quotient.mk (Ideal.span {C u - X * C v})) = eval₂RingHom f s := by
  exact AlgebraicGeometry.RegularPairChart.chart_lift u v f s hs


end HodgeLean.Foundations.Program
