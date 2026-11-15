import HodgeLean.Foundations.Program.SchoenCycleC2NeighbourhoodConormalFramesHelpers
import Mathlib.AlgebraicGeometry.Morphisms.Etale

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An actual immersion over an etale neighbourhood of a smooth base has
local conormal frames with the dimension difference as rank. -/
theorem s2e_etale_neighbourhood_conormal_frames
    (Q W B : Over (Spec ↧ℂ)) (n k : ℕ)
    [SmoothOfRelativeDimension n Q.hom] [SmoothOfRelativeDimension (n + k) B.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (β : W ⟶ B)
    (U : B.left.Opens) (hU : Set.range (ι ≫ β).left ⊆ U)
    (he : Etale (β.left ∣_ U)) :
    ∀ x : Q.left, ∃ V : Q.left.Opens, x ∈ V ∧ Nonempty
      (Scheme.Modules.restrict (s2c_conormal ι.left) V.ι ≅
        (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (Fin k) : V.toScheme.Modules)) := by
  let V := β.left ⁻¹ᵁ U
  letI : Etale (β.left ∣_ U) := he
  letI : SmoothOfRelativeDimension (n + k) (U.ι ≫ B.hom) := by
    simpa only [zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + (n + k)) (U.ι ≫ B.hom))
  have hs : SmoothOfRelativeDimension (n + k) ((β.left ∣_ U) ≫ U.ι ≫ B.hom) := by
    simpa only [zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + (n + k))
        ((β.left ∣_ U) ≫ U.ι ≫ B.hom))
  rw [morphismRestrict_ι_assoc, Over.w β] at hs
  intro x
  apply s2e_conormal_frames_of_smooth_ambient_open Q W n k ι V hs x
  exact hU ⟨x, rfl⟩

end HodgeLean.Foundations.Program
