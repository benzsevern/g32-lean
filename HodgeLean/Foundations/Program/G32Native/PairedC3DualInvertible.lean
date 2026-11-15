import HodgeLean.Foundations.Program.G32Native.PairedC3NativeDualFrames
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Frames.FrameFromTrivialization
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Frames.IsFrameOnPullbackIsoUnit

/-! # Invertibility of the actual native dual line -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- The native internal-Hom dual of an invertible module is invertible,
using the actual local unit-valued functionals as its frames.
Source: Hartshorne, Algebraic Geometry, II.5, invertible sheaves and their duals. -/
theorem paired_c3_dual_invertible {X : Scheme.{0}} {M : X.Modules}
    (hM : IsInvertible M) : IsInvertible M.dual := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hx, ⟨eU⟩⟩ := hM.exists_trivialization x
  obtain ⟨s, hs⟩ := exists_isFrameOn_of_pullback_iso_unit U eU
  exact ⟨U, hx, (paired_c3_native_dual_frame hs).nonempty_pullback_iso_unit U le_rfl le_rfl⟩

#print axioms paired_c3_dual_invertible
end HodgeLean.Foundations.Program.G32Native
