import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # Differential transport for equivalent normal equations

At a zero of the defining equations, only the value of the coefficient operator contributes to their differential.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.TubularEuler

variable {𝕜 E N : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup N] [NormedSpace 𝕜 N]

theorem normal_equation_differential_transport
    (F F' R : E → N) (A : E → N →L[𝕜] N) (p : E)
    (D : E →L[𝕜] N) (B : E →L[𝕜] N →L[𝕜] N)
    (hF : HasFDerivAt F D p) (hA : HasFDerivAt A B p)
    (hzero : F p = 0) (hR : HasFDerivAt R (0 : E →L[𝕜] N) p)
    (hEq : F' =ᶠ[nhds p] (fun x => A x (F x) + R x)) :
    HasFDerivAt F' ((A p).comp D) p := by
  have h := (hA.clm_apply hF).add hR
  have he : ((fun x => A x (F x)) + R) = (fun x => A x (F x) + R x) := rfl
  rw [he] at h
  have h' : HasFDerivAt (fun x => A x (F x) + R x) ((A p).comp D) p := by
    simpa only [hzero, map_zero, add_zero, Pi.add_apply] using h
  exact h'.congr_of_eventuallyEq hEq

theorem normal_equation_differential_covariance
    {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
    (F : E → N) (F' : M → N) (H : E → M) (R : E → N)
    (A : E → N →L[𝕜] N) (p : E)
    (D : E →L[𝕜] N) (D' : M →L[𝕜] N) (L : E →L[𝕜] M)
    (B : E →L[𝕜] N →L[𝕜] N)
    (hF : HasFDerivAt F D p) (hF' : HasFDerivAt F' D' (H p))
    (hH : HasFDerivAt H L p) (hA : HasFDerivAt A B p)
    (hzero : F p = 0) (hR : HasFDerivAt R (0 : E →L[𝕜] N) p)
    (hEq : (F' ∘ H) =ᶠ[nhds p] (fun x => A x (F x) + R x)) :
    D'.comp L = (A p).comp D := by
  have h := normal_equation_differential_transport F (F' ∘ H) R A p D B hF hA hzero hR hEq
  exact (hF'.comp p hH).unique h

#print axioms normal_equation_differential_covariance

#print axioms normal_equation_differential_transport

end HodgeLean.Foundations.TubularEuler
