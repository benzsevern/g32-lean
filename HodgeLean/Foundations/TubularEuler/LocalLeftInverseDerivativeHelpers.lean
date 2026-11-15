import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-! # Injective differentials from local left inverses -/

noncomputable section
set_option maxHeartbeats 200000
open Filter Topology
namespace HodgeLean.Foundations.TubularEuler

theorem localLeftInverse_fderiv_injective
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (r : F → E) (a : E)
    (hf : DifferentiableAt ℝ f a) (hr : DifferentiableAt ℝ r (f a))
    (he : (r ∘ f) =ᶠ[𝓝 a] id) : Function.Injective (fderiv ℝ f a) := by
  have hcomp : HasFDerivAt (r ∘ f)
      ((fderiv ℝ r (f a)).comp (fderiv ℝ f a)) a :=
    hr.hasFDerivAt.comp a hf.hasFDerivAt
  have hder : (fderiv ℝ r (f a)).comp (fderiv ℝ f a) = ContinuousLinearMap.id ℝ E :=
    (hcomp.congr_of_eventuallyEq he.symm).unique (hasFDerivAt_id a)
  intro u v huv
  have hh := congrArg (fderiv ℝ r (f a)) huv
  simpa only [← ContinuousLinearMap.comp_apply, hder, ContinuousLinearMap.id_apply] using hh

end HodgeLean.Foundations.TubularEuler
