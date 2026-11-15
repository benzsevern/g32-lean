import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # The actual critical equation for a Euclidean nearest point

The residual vector is orthogonal to the range of the immersion derivative.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.TubularEuler

/-- At a local minimum of squared distance, the actual immersion derivative
annihilates the residual through its adjoint.
Source: Mathlib, `IsLocalMin.hasFDerivAt_eq_zero`, `HasFDerivAt.norm_sq`,
and `ContinuousLinearMap.adjoint_inner_left`; Lee, Introduction to Smooth
Manifolds, second edition, proof of Theorem 6.24.
HC no distance; AV milestone no distance. -/
theorem nearestPoint_critical_equation
    {B F : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (σ : B → F) (b : B) (y : F) (S : B →L[ℝ] F)
    (hσ : HasFDerivAt σ S b)
    (hmin : IsLocalMin (fun c => ‖σ c - y‖ ^ 2) b) :
    S.adjoint (σ b - y) = 0 := by
  have hd := hmin.hasFDerivAt_eq_zero ((hσ.sub_const y).norm_sq)
  have hv := congrArg (fun A : B →L[ℝ] ℝ => A (S.adjoint (σ b - y))) hd
  simp only [two_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, ContinuousLinearMap.zero_apply] at hv
  rw [← S.adjoint_inner_left] at hv
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  linarith

#print axioms nearestPoint_critical_equation

end HodgeLean.Foundations.TubularEuler
