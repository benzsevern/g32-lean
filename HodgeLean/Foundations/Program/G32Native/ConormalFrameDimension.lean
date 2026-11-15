import HodgeLean.Foundations.Program.G32Native.LocalFrameRank
import HodgeLean.Foundations.Program.SchoenCycleC2SmoothConormalFramesHelpers

/-! Determine conormal-frame rank from smooth ambient and source dimensions. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Any given conormal frame has the dimension-difference rank at its point. -/
theorem g32l4_conormal_frame_rank_eq
    (Q W : Over (Spec ↧ℂ)) (n k : ℕ)
    [SmoothOfRelativeDimension n Q.hom]
    [SmoothOfRelativeDimension (n + k) W.hom]
    (i : Q ⟶ W) [IsClosedImmersion i.left]
    (x : Q.left) (U : Q.left.Opens) (hx : x ∈ U) (m : ℕ)
    (e : Scheme.Modules.restrict (s2c_conormal i.left) U.ι ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin m) : U.toScheme.Modules)) :
    m = k := by
  obtain ⟨V, hxV, ⟨eV⟩⟩ := s2e_smooth_closedImmersion_conormal_frames Q W n k i x
  exact g32l4_local_frame_rank_unique (s2c_conormal i.left) x hx hxV e eV

end HodgeLean.Foundations.Program
