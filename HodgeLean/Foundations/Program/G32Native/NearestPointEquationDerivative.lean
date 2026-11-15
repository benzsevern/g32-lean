import HodgeLean.Foundations.TubularEuler.NormalMetricLiftRegularityHelpers
import HodgeLean.Foundations.Program.G32Native.NearestPointCriticalEquation
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Smoothness and linearization of the nearest-point equation

At a point of the embedded image, the base derivative is the immersion Gram
operator. Frame variation is multiplied by the zero residual.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.TubularEuler

variable {B F : Type*}
variable [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The derivative-orthogonality equation for an actual parametrized image.
Source: Lee, Introduction to Smooth Manifolds, second edition, proof of
Theorem 6.24, Euclidean normal vectors.
For example, at `(σ b,b)` the residual and hence the equation vanish.
HC no distance; AV milestone no distance. -/
def nearestPointEquation (σ : B → F) (p : F × B) : B :=
  (fderiv ℝ σ p.2).adjoint (σ p.2 - p.1)

/-- Analytic parametrizations give an analytic critical equation in both the ambient
point and base coordinates.
Source: Mathlib, `ContDiffAt.fderiv_right`, and `normalAdjoint_contDiff`.
HC no distance; AV milestone no distance. -/
theorem nearestPointEquation_contDiffAt (σ : B → F) (b : B) (y : F)
    (hσ : ContDiffAt ℝ ⊤ σ b) :
    ContDiffAt ℝ ⊤ (nearestPointEquation σ) (y, b) := by
  have hD : ContDiffAt ℝ ⊤ (fderiv ℝ σ) b := hσ.fderiv_right (by simp)
  have hA : ContDiffAt ℝ ⊤ (fun c => (fderiv ℝ σ c).adjoint) b :=
    normalAdjoint_contDiff.contDiffAt.comp b hD
  exact (hA.comp (y, b) contDiffAt_snd).clm_apply
    ((hσ.comp (y, b) contDiffAt_snd).sub contDiffAt_fst)

#print axioms nearestPointEquation_contDiffAt

/-- Along the embedded image, the base derivative of the critical equation is
the Gram operator of the actual parametrization derivative.
Source: Mathlib, `HasFDerivAt.clm_apply`; Lee, Introduction to Smooth
Manifolds, second edition, Euclidean normal-neighbourhood construction.
HC no distance; AV milestone no distance. -/
theorem nearestPointEquation_base_derivative (σ : B → F) (b : B) (S : B →L[ℝ] F)
    (hσ : ContDiffAt ℝ ⊤ σ b) (hS : HasFDerivAt σ S b) :
    HasFDerivAt (fun c => nearestPointEquation σ (σ b, c))
      (S.adjoint.comp S) b := by
  have hD : ContDiffAt ℝ ⊤ (fderiv ℝ σ) b := hσ.fderiv_right (by simp)
  have hA : ContDiffAt ℝ ⊤ (fun c => (fderiv ℝ σ c).adjoint) b :=
    normalAdjoint_contDiff.contDiffAt.comp b hD
  have hd := (hA.differentiableAt (by simp)).hasFDerivAt.clm_apply
    (hS.sub_const (σ b))
  convert hd using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro v
    simp only [sub_self, map_zero, add_zero, hS.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply]

#print axioms nearestPointEquation_base_derivative

/-- Injectivity of the immersion derivative makes the partial derivative in
the base variable invertible in the actual critical equation.
Source: Mathlib, `ContinuousLinearMap.adjoint_comp_self_injective_iff`,
finite-dimensional injective-surjective equivalence, and
`nearestPointEquation_base_derivative`.
HC no distance; AV milestone no distance. -/
theorem nearestPointEquation_base_isInvertible [FiniteDimensional ℝ B]
    (σ : B → F) (b : B) (hσ : ContDiffAt ℝ ⊤ σ b)
    (hinj : Function.Injective (fderiv ℝ σ b)) :
    (fderiv ℝ (nearestPointEquation σ) (σ b, b) ∘L
      ContinuousLinearMap.inr ℝ F B).IsInvertible := by
  let S := fderiv ℝ σ b
  have hS : HasFDerivAt σ S b := (hσ.differentiableAt (by simp)).hasFDerivAt
  have hG := nearestPointEquation_contDiffAt σ b (σ b) hσ
  have hinc : HasFDerivAt (fun c : B => (σ b, c))
      (ContinuousLinearMap.inr ℝ F B) b :=
    (hasFDerivAt_const (σ b) b).prodMk (hasFDerivAt_id b)
  have hpart : fderiv ℝ (nearestPointEquation σ) (σ b, b) ∘L
      ContinuousLinearMap.inr ℝ F B = S.adjoint.comp S :=
    (((hG.differentiableAt (by simp)).hasFDerivAt).comp b hinc).unique
      (nearestPointEquation_base_derivative σ b S hσ hS)
  rw [hpart]
  have hGram : Function.Injective (S.adjoint.comp S) :=
    S.adjoint_comp_self_injective_iff.mpr hinj
  let A := ContinuousLinearEquiv.ofBijective (S.adjoint.comp S)
    (LinearMap.ker_eq_bot.mpr hGram)
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hGram))
  exact ⟨A, rfl⟩

#print axioms nearestPointEquation_base_isInvertible

end HodgeLean.Foundations.TubularEuler
