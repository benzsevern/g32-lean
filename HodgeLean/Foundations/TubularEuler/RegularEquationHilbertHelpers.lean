import HodgeLean.Foundations.TubularEuler.RegularEquationAnalyticHelpers
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! # Original regular equations in Hilbert coordinate models

Fixed complex linear coordinate equivalences preserve analytic regularity and transverse surjectivity.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.TubularEuler

variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
variable [IsScalarTower ℝ ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup N] [NormedSpace ℂ N] [NormedSpace ℝ N]
variable [IsScalarTower ℝ ℂ N] [CompleteSpace N]

def complexContinuousLinearEquivReal (L : E ≃L[ℂ] N) : E ≃L[ℝ] N where
  toLinearEquiv := L.toLinearEquiv.restrictScalars ℝ
  continuous_toFun := L.continuous
  continuous_invFun := L.symm.continuous

#print axioms complexContinuousLinearEquivReal

theorem exists_regular_equation_hilbert_submersion
    (X Y : Over (Spec (CommRingCat.of ℂ))) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (k : ℕ) [SmoothOfRelativeDimension k Y.hom] [SmoothOfRelativeDimension (k + k) X.hom]
    (L : E ≃L[ℂ] (Fin (k + k) → ℂ)) (A : N ≃L[ℂ] (Fin k → ℂ))
    (V : X.left.Opens) (hV : IsAffineOpen V) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ V))
    (z : ComplexPoint X) (hz : Point.map j x ∈ (chartAt (Fin (k + k) → ℂ) z).source) :
    ∃ u : Fin k → RingHom.ker (j.left.app V).hom,
      let F : E → N := fun a => A.symm (fun i =>
        Point.evaluate V (u i).val ((chartAt (Fin (k + k) → ℂ) z).symm (L a)))
      let p := L.symm ((chartAt (Fin (k + k) → ℂ) z) (Point.map j x))
      AnalyticAt ℝ F p ∧ Function.Surjective (fderiv ℝ F p) := by
  obtain ⟨u, hu⟩ := exists_regular_conormal_submersion X Y j k V hV x hx z hz
  refine ⟨u, ?_⟩
  let f : (Fin (k + k) → ℂ) → (Fin k → ℂ) := fun a i =>
    Point.evaluate V (u i).val ((chartAt (Fin (k + k) → ℂ) z).symm a)
  let p := L.symm ((chartAt (Fin (k + k) → ℂ) z) (Point.map j x))
  have hf : AnalyticAt ℂ f (L p) := by
    simpa only [p, L.apply_symm_apply] using
      regular_equation_vector_analyticAt X (k + k) k V (fun i => (u i).val)
        z (Point.map j x) hz hx
  have ha : AnalyticAt ℂ (fun a : E => A.symm (f (L a))) p :=
    (A.symm.toContinuousLinearMap.analyticAt _).comp
      (hf.comp (L.toContinuousLinearMap.analyticAt _))
  refine ⟨ha.restrictScalars, ?_⟩
  let D := A.symm.toContinuousLinearMap.comp
    ((fderiv ℂ f (L p)).comp L.toContinuousLinearMap)
  have hd : HasFDerivAt (fun a : E => A.symm (f (L a))) D p :=
    A.symm.toContinuousLinearMap.hasFDerivAt.comp p
      (hf.hasStrictFDerivAt.hasFDerivAt.comp p L.toContinuousLinearMap.hasFDerivAt)
  have hs : Function.Surjective D := by
    have hu' : Function.Surjective (fderiv ℂ f (L p)) := by
      simpa only [p, L.apply_symm_apply] using hu
    exact A.symm.surjective.comp (hu'.comp L.surjective)
  rw [(hd.restrictScalars ℝ).fderiv]
  exact hs

#print axioms exists_regular_equation_hilbert_submersion

end HodgeLean.Foundations.TubularEuler
