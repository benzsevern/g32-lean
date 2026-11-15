import HodgeLean.Foundations.Program.SchoenHomogeneousDomains
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Properties

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry HomogeneousLocalization
namespace HodgeLean.Foundations.Program

/-- The actual Proj scheme of a graded domain is reduced. -/
theorem s2_proj_isReduced_of_domain {A : Type} [CommRing A] [IsDomain A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] : IsReduced (Proj 𝒜) := by
  apply +allowSynthFailures isReduced_of_isReduced_stalk
  intro p
  let P := p.asHomogeneousIdeal.toIdeal
  haveI : P.IsPrime := p.isPrime
  haveI : IsDomain (AtPrime 𝒜 P) :=
    Function.Injective.isDomain
      (algebraMap (AtPrime 𝒜 P) (Localization.AtPrime P))
      (HomogeneousLocalization.val_injective (𝒜 := 𝒜) (x := P.primeCompl))
  haveI : IsDomain ((Proj 𝒜).presheaf.stalk p) :=
    (Proj.stalkIso' 𝒜 p).toMulEquiv.isDomain
  infer_instance

end HodgeLean.Foundations.Program
