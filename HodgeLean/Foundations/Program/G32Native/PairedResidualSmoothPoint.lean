import HodgeLean.Foundations.Program.G32Native.PairedResidualPointFrame
import HodgeLean.Foundations.Program.SchoenCycleC2SmoothConormalFramesHelpers

/-! # The conormal of a complex point in a smooth base -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- A specified point of a smooth base has a global conormal frame of the base dimension. -/
def residual_smooth_point_conormal_iso
    (Y : Over (Spec ↧ℂ)) (k : ℕ) [SmoothOfRelativeDimension k Y.hom]
    (z : Over.mk (𝟙 (Spec ↧ℂ)) ⟶ Y) [IsClosedImmersion z.left] :
    s2c_conormal z.left ≅
      (SheafOfModules.free (R := (Spec ↧ℂ).ringCatSheaf) (Fin k) : (Spec ↧ℂ).Modules) := by
  letI : SmoothOfRelativeDimension 0 (Over.mk (𝟙 (Spec ↧ℂ))).hom :=
    inferInstanceAs (SmoothOfRelativeDimension 0 (𝟙 (Spec ↧ℂ)))
  letI : SmoothOfRelativeDimension (0 + k) Y.hom := by
    simpa only [zero_add] using (inferInstance : SmoothOfRelativeDimension k Y.hom)
  exact residual_global_frame_of_subsingleton (X := Spec ↧ℂ) _ k
    (s2e_smooth_closedImmersion_conormal_frames _ Y 0 k z)

#print axioms residual_smooth_point_conormal_iso

end HodgeLean.Foundations.Program.G32Native
