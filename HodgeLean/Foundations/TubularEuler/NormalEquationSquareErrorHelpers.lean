import HodgeLean.Foundations.TubularEuler.NormalEquationDifferentialHelpers
import HodgeLean.Adapters.NormalConeB4aGysinBridge2DifferentialComparison
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! # Zero differential for actual regular square-error vectors

The components are evaluated from original scheme sections whose germs lie in the maximal-ideal square.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Adapters

theorem normal_regular_square_error_hasFDerivAt_zero
    (X : Over (Spec (CommRingCat.of ℂ))) (d k : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source)
    (W : X.left.Opens) (hW : x.underlying ∈ W) (s : Fin k → Γ(X.left, W))
    (hsq : ∀ i, X.left.presheaf.germ W x.underlying hW (s i) ∈
      IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying) ^ 2) :
    HasFDerivAt
      (fun a : Fin d → ℂ => fun i : Fin k => Point.evaluate W (s i)
        ((chartAt (Fin d → ℂ) z).symm a))
      (0 : (Fin d → ℂ) →L[ℂ] (Fin k → ℂ)) ((chartAt (Fin d → ℂ) z) x) := by
  apply hasFDerivAt_pi'.mpr
  intro i
  have h := a3b4g_hasFDerivAt_zero_of_mem_sq X z x hx
    (X.left.presheaf.germ W x.underlying hW (s i)) (hsq i) W hW (s i) rfl
  simpa only [ContinuousLinearMap.comp_zero] using h

theorem normal_regular_equation_differential_covariance
    (X : Over (Spec (CommRingCat.of ℂ))) (d k : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source)
    (W : X.left.Opens) (hW : x.underlying ∈ W) (s : Fin k → Γ(X.left, W))
    (hsq : ∀ i, X.left.presheaf.germ W x.underlying hW (s i) ∈
      IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying) ^ 2)
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
    (F : (Fin d → ℂ) → (Fin k → ℂ)) (F' : M → (Fin k → ℂ)) (H : (Fin d → ℂ) → M)
    (A : (Fin d → ℂ) → (Fin k → ℂ) →L[ℂ] (Fin k → ℂ))
    (D : (Fin d → ℂ) →L[ℂ] (Fin k → ℂ)) (D' : M →L[ℂ] (Fin k → ℂ))
    (L : (Fin d → ℂ) →L[ℂ] M)
    (B : (Fin d → ℂ) →L[ℂ] (Fin k → ℂ) →L[ℂ] (Fin k → ℂ))
    (hF : HasFDerivAt F D ((chartAt (Fin d → ℂ) z) x))
    (hF' : HasFDerivAt F' D' (H ((chartAt (Fin d → ℂ) z) x)))
    (hH : HasFDerivAt H L ((chartAt (Fin d → ℂ) z) x))
    (hA : HasFDerivAt A B ((chartAt (Fin d → ℂ) z) x))
    (hzero : F ((chartAt (Fin d → ℂ) z) x) = 0)
    (hEq : (F' ∘ H) =ᶠ[nhds ((chartAt (Fin d → ℂ) z) x)]
      (fun a => A a (F a) + fun i => Point.evaluate W (s i) ((chartAt (Fin d → ℂ) z).symm a))) :
    D'.comp L = (A ((chartAt (Fin d → ℂ) z) x)).comp D := by
  exact normal_equation_differential_covariance F F' H
    (fun a i => Point.evaluate W (s i) ((chartAt (Fin d → ℂ) z).symm a)) A
    ((chartAt (Fin d → ℂ) z) x) D D' L B hF hF' hH hA hzero
    (normal_regular_square_error_hasFDerivAt_zero X d k z x hx W hW s hsq) hEq

#print axioms normal_regular_equation_differential_covariance

#print axioms normal_regular_square_error_hasFDerivAt_zero

end HodgeLean.Foundations.TubularEuler
