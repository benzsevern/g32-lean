import HodgeLean.Foundations.Program.SchoenTowerConormalDefs

/-! # Restricting the actual global free conormal comparison -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A global frame restricts to a frame on the specified scheme open. -/
def residual_restrict_free_iso {X : Scheme.{0}} (M : X.Modules) (k : ℕ)
    (e : M ≅ (SheafOfModules.free (R := X.ringCatSheaf) (Fin k) : X.Modules))
    (U : X.Opens) :
    Scheme.Modules.restrict M U.ι ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) : U.toScheme.Modules) := by
  letI : (SheafOfModules.pushforward.{0} U.ι.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward U.ι).IsRightAdjoint
  exact (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫
    (Scheme.Modules.pullback U.ι).mapIso e ≪≫
    SheafOfModules.pullbackObjFreeIso U.ι.toRingCatSheafHom (Fin k)

#print axioms residual_restrict_free_iso

end HodgeLean.Foundations.Program.G32Native
