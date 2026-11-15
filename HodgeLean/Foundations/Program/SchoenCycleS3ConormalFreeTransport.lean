import HodgeLean.Foundations.Program.SchoenCycleS3ConormalIsoTransport

/-! # Free-module transport along scheme isomorphisms -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A free pullback along a scheme isomorphism transports to a free module on the target. -/
def s2e_freeOfPullbackIso {X Y : Scheme.{0}} (e : X ≅ Y) (M : Y.Modules) (ι : Type)
    (h : (Scheme.Modules.pullback e.hom).obj M ≅
      (SheafOfModules.free (R := X.ringCatSheaf) ι : X.Modules)) :
    M ≅ (SheafOfModules.free (R := Y.ringCatSheaf) ι : Y.Modules) :=
  ((Scheme.Modules.pullbackComp e.inv e.hom).app M ≪≫
    (Scheme.Modules.pullbackCongr e.inv_hom_id).app M ≪≫
      (Scheme.Modules.pullbackId Y).app M).symm ≪≫
    (Scheme.Modules.pullback e.inv).mapIso h ≪≫
      SheafOfModules.pullbackObjFreeIso e.inv.toRingCatSheafHom ι

end HodgeLean.Foundations.Program
