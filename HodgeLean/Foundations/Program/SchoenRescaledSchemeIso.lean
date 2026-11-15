import HodgeLean.Foundations.Program.SchoenRescaledScheme
import Mathlib.AlgebraicGeometry.OpenImmersion

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory
namespace HodgeLean.Foundations.Program
namespace S2RescaledProj

variable {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ) (hD : 0 < D)
    [GradedRing (fun n => 𝒜 (D * n))]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Positive degree rescaling preserves the actual Proj scheme. -/
theorem map_isIso : IsIso (map 𝒜 D hD) := by
  rw [isIso_iff_isIso_stalkMap]
  refine ⟨?_, map_stalkMap_isIso 𝒜 D hD⟩
  exact (TopCat.isoOfHomeo (X := TopCat.of (ProjectiveSpectrum 𝒜))
    (Y := TopCat.of (ProjectiveSpectrum (fun n => 𝒜 (D * n))))
    (s2_rescaledProjHomeomorph 𝒜 D hD)).isIso_hom

/-- The actual Proj scheme isomorphism for a grading supported on multiples of a positive degree. -/
def iso : Proj 𝒜 ≅ Proj (fun n => 𝒜 (D * n)) := by
  letI := map_isIso 𝒜 D hD
  exact asIso (map 𝒜 D hD)

end S2RescaledProj
end HodgeLean.Foundations.Program
