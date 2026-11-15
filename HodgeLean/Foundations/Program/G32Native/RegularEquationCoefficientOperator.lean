import HodgeLean.Foundations.TubularEuler.NormalFrameRegularCoefficientHelpers
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Operators formed from regular equation coefficients -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler

/-- The row indexed by an equation evaluates that equation's coefficients
against the normal-frame coordinates.
Source: Mathlib, `ContinuousLinearEquiv.piRing`; regular evaluation on
complex points. -/
def regularEquationCoefficientOperator
    (Y : Over (Spec ↧ℂ)) (k : ℕ) (U : Y.left.Opens)
    (r : Fin k → Fin k → Γ(Y.left, U)) (x : ComplexPoint Y) :
    (Fin k → ℂ) →L[ℂ] (Fin k → ℂ) :=
  (ContinuousLinearEquiv.piRing (𝕜 := ℂ) (E := Fin k → ℂ) (Fin k)).symm
    (fun a i => Point.evaluate U (r i a) x)

theorem regularEquationCoefficientOperator_apply
    (Y : Over (Spec ↧ℂ)) (k : ℕ) (U : Y.left.Opens)
    (r : Fin k → Fin k → Γ(Y.left, U)) (x : ComplexPoint Y)
    (w : Fin k → ℂ) (i : Fin k) :
    regularEquationCoefficientOperator Y k U r x w i =
      ∑ a, w a * Point.evaluate U (r i a) x := by
  change ((LinearEquiv.piRing ℂ (Fin k → ℂ) (Fin k) ℂ).symm
    (fun a i => Point.evaluate U (r i a) x) w) i = _
  rw [LinearEquiv.piRing_symm_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The coefficient operator varies analytically on the original base open.
Source: `Analytic.f4_isHolFun_evaluate` and
`Analytic.f4_isHolFun_iff_contMDiffOn`. -/
theorem regularEquationCoefficientOperator_contMDiffOn
    (Y : Over (Spec ↧ℂ)) (k m : ℕ) [SmoothOfRelativeDimension m Y.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (U : Y.left.Opens) (r : Fin k → Fin k → Γ(Y.left, U)) :
    ContMDiffOn 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, (Fin k → ℂ) →L[ℂ] (Fin k → ℂ)) ω
      (regularEquationCoefficientOperator Y k U r) (Point.overOpen U) := by
  have hc : ContMDiffOn 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin k → Fin k → ℂ) ω
      (fun x : ComplexPoint Y => fun a i => Point.evaluate U (r i a) x)
      (Point.overOpen U) := by
    apply contMDiffOn_pi_space.mpr
    intro a
    apply contMDiffOn_pi_space.mpr
    intro i
    exact (HodgeLean.Foundations.Analytic.f4_isHolFun_iff_contMDiffOn Y m
      (fun x => Point.evaluate U (r i a) x) (Point.isOpen_overOpen U)).mp
      (HodgeLean.Foundations.Analytic.f4_isHolFun_evaluate Y U (r i a))
  exact (ContinuousLinearEquiv.piRing (𝕜 := ℂ) (E := Fin k → ℂ)
    (Fin k)).symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn hc

/-- Coefficients of the standard basis give the identity operator.
Source: `regularEquationCoefficientOperator_apply`. -/
theorem regularEquationCoefficientOperator_eq_id
    (Y : Over (Spec ↧ℂ)) (k : ℕ) (U : Y.left.Opens)
    (r : Fin k → Fin k → Γ(Y.left, U)) (x : ComplexPoint Y)
    (hr : ∀ i a, Point.evaluate U (r i a) x = if a = i then 1 else 0) :
    regularEquationCoefficientOperator Y k U r x =
      ContinuousLinearMap.id ℂ (Fin k → ℂ) := by
  ext w i
  rw [regularEquationCoefficientOperator_apply]
  simp only [hr, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, ContinuousLinearMap.id_apply]

#print axioms regularEquationCoefficientOperator_eq_id

#print axioms regularEquationCoefficientOperator_apply
#print axioms regularEquationCoefficientOperator_contMDiffOn
end HodgeLean.Foundations.TubularEuler
