import HodgeLean.Foundations.Program.G32Native.PairedConormalFunctorRelation
import HodgeLean.Foundations.Program.G32Native.PairedConormalPullbackAdditive
import HodgeLean.Foundations.Curves.Picard.LineBundles.Transport

/-! # Canonical pullback comparisons for actual elementary presentation sources -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Curves.Picard.LineBundles

/-- The actual presentation source is transported through its canonical
biproduct, unit, and free-module pullback comparisons. -/
def conormalUnitFreePullbackIso {X Y : Scheme.{0}} (f : X ⟶ Y) (k : ℕ) :
    (Scheme.Modules.pullback f).obj
      (SheafOfModules.unit Y.ringCatSheaf ⊞
        SheafOfModules.free (R := Y.ringCatSheaf) (Fin k)) ≅
      (SheafOfModules.unit X.ringCatSheaf ⊞
        SheafOfModules.free (R := X.ringCatSheaf) (Fin k)) := by
  let F := Scheme.Modules.pullback f
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  exact F.mapBiprod _ _ ≪≫ biprod.mapIso (pullbackUnit f)
    (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (Fin k))

/-- The same canonical source comparison retains both literal pulled relation components. -/
theorem conormal_unit_free_pullback_relation {X Y : Scheme.{0}} (f : X ⟶ Y)
    (k : ℕ) {I : Y.Modules} (a : I ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (b : I ⟶ SheafOfModules.free (R := Y.ringCatSheaf) (Fin k)) :
    (Scheme.Modules.pullback f).map (HodgeLean.Foundations.NormalPresentation.relation a b) ≫
      (conormalUnitFreePullbackIso f k).hom =
      HodgeLean.Foundations.NormalPresentation.relation
        ((Scheme.Modules.pullback f).map a ≫ (pullbackUnit f).hom)
        ((Scheme.Modules.pullback f).map b ≫
          (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (Fin k)).hom) := by
  let F := Scheme.Modules.pullback f
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  exact conormal_functor_relation_transport F a b (pullbackUnit f)
    (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (Fin k))

end HodgeLean.Foundations.Program.G32Native
