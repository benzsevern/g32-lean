import HodgeLean.Foundations.Program.SchoenHomogeneousLocalizationMaps
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open HomogeneousLocalization
namespace HodgeLean.Foundations.Program

/-- Homogeneous localization of a domain away from a nonzero element is a domain. -/
theorem s2_homogeneousAway_isDomain {A : Type} [CommRing A] [IsDomain A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (a : A) (ha : a ≠ 0) :
    IsDomain (Away 𝒜 a) := by
  letI : IsDomain (Localization (Submonoid.powers a)) := IsLocalization.Away.isDomain _ ha
  exact Function.Injective.isDomain
    (algebraMap (Away 𝒜 a) (Localization (Submonoid.powers a)))
    (HomogeneousLocalization.val_injective (𝒜 := 𝒜) (x := Submonoid.powers a))

end HodgeLean.Foundations.Program
