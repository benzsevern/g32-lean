import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateDualGenerators
import HodgeLean.Foundations.Program.G32Native.PairedC3InitialCoordinateLocalFrames
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Frames.IsFrameOnPullbackIsoUnit

/-! # Negative summand frames on the specified coordinate cover -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- The native dual coordinate generator gives a rank-one frame on its
specified standard open, with no further shrinking. -/
def pairedC3NegativeCoordinateOpenFrame (k : ℕ) (i : Fin (k + 1)) :
    (Scheme.Modules.pullback (ProjSpace.standardOpen ℂ k i).ι).obj
      (pairedC3NegativeLine k) ≅
      (SheafOfModules.free (R := (ProjSpace.standardOpen ℂ k i).toScheme.ringCatSheaf)
        (Fin 1) : (ProjSpace.standardOpen ℂ k i).toScheme.Modules) := by
  let e := Classical.choice ((paired_c3_coordinate_dual_generator_frame k i).nonempty_pullback_iso_unit (ProjSpace.standardOpen ℂ k i) le_rfl le_rfl)
  exact e ≪≫ (coproductUniqueIso
    (fun _ : Fin 1 => SheafOfModules.unit (ProjSpace.standardOpen ℂ k i).toScheme.ringCatSheaf)).symm

/-- The recursive split bundle is free of its stated rank on every
specified standard open of the parameter scheme. -/
def pairedC3SplitCoordinateOpenFrame (k a b : ℕ) (i : Fin (k + 1)) :
    (Scheme.Modules.pullback (ProjSpace.standardOpen ℂ k i).ι).obj
      (pairedC3SplitBundle k a b) ≅
      (SheafOfModules.free (R := (ProjSpace.standardOpen ℂ k i).toScheme.ringCatSheaf)
        (Fin (a + b)) : (ProjSpace.standardOpen ℂ k i).toScheme.Modules) := by
  let U := ProjSpace.standardOpen ℂ k i
  let F := Scheme.Modules.pullback U.ι
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  induction b with
  | zero => exact SheafOfModules.pullbackObjFreeIso U.ι.toRingCatSheafHom (Fin a)
  | succ b ih =>
    exact F.mapBiprod _ _ ≪≫
      biprod.mapIso ih (pairedC3NegativeCoordinateOpenFrame k i) ≪≫
      biprod.isoCoprod _ _ ≪≫ SheafOfModules.freeSumIso (Fin (a + b)) (Fin 1) ≪≫
      SheafOfModules.freeFunctor.mapIso finSumFinEquiv.toIso

/-- The standard initial conormal and its prescribed split bundle are
isomorphic on each original standard open. This comparison alone carries
no assertion about intersections of different standard opens. -/
def pairedC3InitialCoordinateLocalComparison (k r : ℕ) (hr : 0 < r)
    (i : Fin (k + 1)) :
    (Scheme.Modules.pullback (ProjSpace.standardOpen ℂ k i).ι).obj
        (HodgeLean.Foundations.Program.s2c_conormal (pairedC3InitialCoordinateInclusion k r hr)) ≅
      (Scheme.Modules.pullback (ProjSpace.standardOpen ℂ k i).ι).obj
        (pairedC3SplitBundle k 0 (r - 1)) := by
  exact pairedC3InitialCoordinateOpenFrame k r hr i ≪≫
    (by simpa only [Nat.zero_add] using
      (pairedC3SplitCoordinateOpenFrame k 0 (r - 1) i).symm)

end HodgeLean.Foundations.Program.G32Native
