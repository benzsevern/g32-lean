import HodgeLean.Foundations.Program.SchoenHomogeneousLocalizationMaps
import HodgeLean.Foundations.Program.SchoenFixedRingGrading

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open HomogeneousLocalization
namespace HodgeLean.Foundations.Program

/-- An actual homogeneous subring chart map into a domain is injective away from zero. -/
theorem s2_subringAwayMap_injective {A : Type} [CommRing A] [IsDomain A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (R : Subring A)
    [GradedRing (s2_subringGradedPiece 𝒜 R)] (f : R) (hf : (f : A) ≠ 0) :
    Function.Injective (Away.map (s2_subringGradedInclusion 𝒜 R) f) := by
  apply s2_homogeneousLocalization_map_injective
  · rintro ⟨n, hn⟩
    exact pow_ne_zero n hf hn
  · exact Subtype.val_injective

end HodgeLean.Foundations.Program
