import HodgeLean.Foundations.Program.G32Native.PairedResidualFlatFibre

/-! # The unit conormal of a fibre over a smooth curve -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- A flat fibre over a specified point of a smooth curve has the unit conormal. -/
def residual_curve_fibre_conormal_unit
    {S T : Scheme.{0}} (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    (z : Over.mk (𝟙 (Spec ↧ℂ)) ⟶ Y) [IsClosedImmersion z.left]
    (s : S ⟶ T) [IsClosedImmersion s]
    (f : T ⟶ Y.left) [Flat f] (p : S ⟶ Spec ↧ℂ)
    (sq : IsPullback p s z.left f) :
    s2c_conormal s ≅ (SheafOfModules.unit S.ringCatSheaf : S.Modules) :=
  (Scheme.Modules.pullbackId S).symm.app (s2c_conormal s) ≪≫
    residual_flat_fibre_source_iso Y 1 z s f p sq (𝟙 S) ≪≫
    coproductUniqueIso (fun _ : Fin 1 => SheafOfModules.unit S.ringCatSheaf)

#print axioms residual_curve_fibre_conormal_unit

end HodgeLean.Foundations.Program.G32Native
