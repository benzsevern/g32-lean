import HodgeLean.Foundations.Program.G32Native.PairedConormalLocalFrameIso
import HodgeLean.Foundations.Program.SchoenCycleC2SmoothConormalFramesHelpers

/-! # Local freeness of the actual smooth conormal and its specified model -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native

/-- A smooth immersion's actual conormal is locally free, from its frames
at every scheme point. -/
theorem paired_smooth_conormal_locallyFree
    (Q W : Over (Spec ↧ℂ)) (n k : ℕ)
    [SmoothOfRelativeDimension n Q.hom]
    [SmoothOfRelativeDimension (n + k) W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] :
    (s2c_conormal ι.left).IsLocallyFree := by
  apply paired_module_locallyFree_of_pullbackFrames
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := s2e_smooth_closedImmersion_conormal_frames Q W n k ι x
  exact ⟨U, hx, Fin k, ⟨e.symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app (s2c_conormal ι.left)⟩⟩

/-- The specified conormal model on any isomorphic scheme is locally free;
local freeness of that model is a consequence rather than an extra input. -/
theorem paired_smooth_conormal_model_locallyFree
    (Q W : Over (Spec ↧ℂ)) (n k : ℕ)
    [SmoothOfRelativeDimension n Q.hom]
    [SmoothOfRelativeDimension (n + k) W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left]
    (Y : Scheme) (e : Q.left ≅ Y) (M : Y.Modules)
    (E : s2c_conormal ι.left ≅ (Scheme.Modules.pullback e.hom).obj M) :
    M.IsLocallyFree := by
  letI := paired_smooth_conormal_locallyFree Q W n k ι
  letI := paired_module_locallyFree_of_iso E
  exact paired_module_locallyFree_of_isoPullback e M

/-- The actual smooth conormal model has rank-k frames at every scheme point,
with the specified model isomorphism retained. -/
theorem paired_smooth_conormal_model_frames
    (Q W : Over (Spec ↧ℂ)) (n k : ℕ)
    [SmoothOfRelativeDimension n Q.hom]
    [SmoothOfRelativeDimension (n + k) W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left]
    (Y : Scheme) (e : Q.left ≅ Y) (M : Y.Modules)
    (E : s2c_conormal ι.left ≅ (Scheme.Modules.pullback e.hom).obj M) :
    ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧
      Nonempty (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) ≅
        (Scheme.Modules.pullback U.ι).obj M) := by
  apply paired_module_fixedFrames_of_isoPullback e (s2c_conormal ι.left) M E (Fin k)
  intro x
  obtain ⟨U, hx, ⟨b⟩⟩ := s2e_smooth_closedImmersion_conormal_frames Q W n k ι x
  exact ⟨U, hx, ⟨b.symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app (s2c_conormal ι.left)⟩⟩

end HodgeLean.Foundations.Program.G32Native
