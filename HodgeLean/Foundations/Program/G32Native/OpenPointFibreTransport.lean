import HodgeLean.Foundations.Program.G32Native.ModuleSectionValueUnit

/-! # Restricting an actual module fibre to an ambient open -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native

/-- Pullback composition identifies the original module fibre with its
fibre computed on an actual open containing the point. -/
def openPointFibreEquiv {W : Over (Spec ↧ℂ)} (M : W.left.Modules)
    (U : W.left.Opens) (p : ComplexPoint W) (hp : p ∈ Point.overOpen U) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback (liftToOpen W U p hp)).obj
        ((Scheme.Modules.pullback U.ι).obj M)) ≃ₗ[ℂ]
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback p.left).obj M) :=
  ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
    ((Scheme.Modules.pullbackComp (liftToOpen W U p hp) U.ι).app M ≪≫
      (Scheme.Modules.pullbackCongr (liftToOpen_fac W U p hp)).app M)).toLinearEquiv

/-- The open-fibre comparison retains the specialization of the original
local module section. -/
theorem openPointFibreEquiv_localSection {W : Over (Spec ↧ℂ)} (M : W.left.Modules)
    (U : W.left.Opens) (p : ComplexPoint W) (hp : p ∈ Point.overOpen U)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj M) :
    openPointFibreEquiv M U p hp
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        ((Scheme.Modules.pullback (liftToOpen W U p hp)).map s)
        ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
          (HodgeLean.Foundations.Curves.Picard.LineBundles.pullbackUnit (liftToOpen W U p hp)).inv
          (1 : Γ(Spec ↧ℂ, ⊤)))) = moduleSectionValue M U s p hp := by
  unfold openPointFibreEquiv moduleSectionValue
  simp only [Iso.toLinearEquiv_apply, Functor.mapIso_hom, Iso.trans_hom,
    CategoryTheory.Functor.map_comp, ModuleCat.comp_apply]
  rfl

#print axioms openPointFibreEquiv
#print axioms openPointFibreEquiv_localSection
end HodgeLean.Foundations.Program.G32Native
