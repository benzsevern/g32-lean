import HodgeLean.Foundations.Program.G32Native.PairedResidualSmoothPoint
import HodgeLean.Foundations.AlgebraicGeometry.ConormalBaseChange

/-! # The free source conormal of a flat fibre over a smooth base -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The actual fibre conormal remains free after pullback to its retained component. -/
def residual_flat_fibre_source_iso
    {P T V : Scheme.{0}} (Y : Over (Spec ↧ℂ)) (k : ℕ)
    [SmoothOfRelativeDimension k Y.hom]
    (z : Over.mk (𝟙 (Spec ↧ℂ)) ⟶ Y) [IsClosedImmersion z.left]
    (t : T ⟶ V) [IsClosedImmersion t]
    (f : V ⟶ Y.left) [Flat f] (p : T ⟶ Spec ↧ℂ)
    (sq : IsPullback p t z.left f) (a : P ⟶ T) :
    (Scheme.Modules.pullback a).obj (s2c_conormal t) ≅
      (SheafOfModules.free (R := P.ringCatSheaf) (Fin k) : P.Modules) := by
  let e := Conormal.flatBaseChangeIso z.left t f p sq
  letI : (SheafOfModules.pushforward.{0} (a ≫ p).toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward (a ≫ p)).IsRightAdjoint
  exact (Scheme.Modules.pullback a).mapIso e.symm ≪≫
    (Scheme.Modules.pullbackComp a p).app (s2c_conormal z.left) ≪≫
    (Scheme.Modules.pullback (a ≫ p)).mapIso (residual_smooth_point_conormal_iso Y k z) ≪≫
    SheafOfModules.pullbackObjFreeIso (a ≫ p).toRingCatSheafHom (Fin k)

#print axioms residual_flat_fibre_source_iso

end HodgeLean.Foundations.Program.G32Native
