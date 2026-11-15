import HodgeLean.Foundations.Program.G32Native.PairedResidualCurveFibre

/-! # Pushing the residual fibre conormal to its specified intersection image -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The residual fibre conormal pushes to the unit on the same specified intersection subscheme. -/
def residual_flat_curve_last_iso
    {S T P H : Scheme.{0}} (Y : Over (Spec ↧ℂ))
    [SmoothOfRelativeDimension 1 Y.hom]
    (z : Over.mk (𝟙 (Spec ↧ℂ)) ⟶ Y) [IsClosedImmersion z.left]
    (s : S ⟶ T) [IsClosedImmersion s]
    (f : T ⟶ Y.left) [Flat f] (p : S ⟶ Spec ↧ℂ)
    (sq : IsPullback p s z.left f)
    (a : S ⟶ P) (h : H ⟶ P) (e : S ≅ H) (he : e.hom ≫ h = a) :
    (Scheme.Modules.pushforward a).obj (s2c_conormal s) ≅
      (Scheme.Modules.pushforward h).obj (SheafOfModules.unit H.ringCatSheaf) := by
  letI : IsIso (SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom) :=
    s2e_unitPushforward_isIso e.hom
  exact (Scheme.Modules.pushforward a).mapIso
      (residual_curve_fibre_conormal_unit Y z s f p sq) ≪≫
    (Scheme.Modules.pushforwardCongr he.symm).app (SheafOfModules.unit S.ringCatSheaf) ≪≫
    (Scheme.Modules.pushforwardComp e.hom h).symm.app (SheafOfModules.unit S.ringCatSheaf) ≪≫
    (Scheme.Modules.pushforward h).mapIso
      (asIso (SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom)).symm

#print axioms residual_flat_curve_last_iso

end HodgeLean.Foundations.Program.G32Native
