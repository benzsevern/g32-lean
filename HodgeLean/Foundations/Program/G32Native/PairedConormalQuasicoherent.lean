import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Quasicoherent.QuasicoherentCokernel
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Quasicoherence of the original quotient and its open pullback -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- The last original object in a short exact sequence is quasicoherent when the first two are. -/
theorem conormal_shortExact_last_quasicoherent {X : Scheme} (S : ShortComplex X.Modules)
    (hs : S.ShortExact) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] :
    S.X₃.IsQuasicoherent := by
  have hq : (cokernel S.f).IsQuasicoherent := isQuasicoherent_cokernel S.f
  let e : cokernel S.f ≅ S.X₃ :=
    (cokernelIsCokernel S.f).coconePointUniqueUpToIso hs.gIsCokernel
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((sheafOfModulesEquivalence X).functor.mapIso e) hq

/-- Actual pullback along an open immersion preserves quasicoherence. -/
theorem conormal_open_pullback_quasicoherent {X Y : Scheme} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj M).IsQuasicoherent := by
  have hq : ((restrictFunctor f).obj M).IsQuasicoherent :=
    isQuasicoherent_restrictFunctor f M
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((sheafOfModulesEquivalence X).functor.mapIso ((restrictFunctorIsoPullback f).app M)) hq

end HodgeLean.Foundations.Program.G32Native
