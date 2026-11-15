import HodgeLean.Foundations.Program.G32Native.ConormalSectionIsoNaturality
import HodgeLean.Foundations.Program.G32Native.ConormalIdealInclusionNaturality

/-! # Equality transport of original conormal sections -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution

/-- The source comparison transports the conormal image of the typed ideal section. -/
theorem conormalSection_source_iso_typed {Q Q' W : Scheme.{0}}
    (j : Q ⟶ W) (e : Q' ≅ Q)
    (s : SheafOfModules.unit.{0} W.ringCatSheaf ⟶ Conormal.idealModule j) :
    i1_module_sectionPullback e.hom (Conormal.sheaf j)
        (i1_module_sectionPullback j (Conormal.idealModule j) s) ≫
      (HodgeLean.Foundations.Program.s2e_conormal_source_iso j e).hom =
    i1_module_sectionPullback (e.hom ≫ j) (Conormal.idealModule (e.hom ≫ j))
      (conormalSourceIdealSection j e s) :=
  conormalSection_source_iso j e s

/-- Equality of immersion maps transports both the ideal section and its conormal image. -/
theorem conormalSection_hom_eq {Q W : Scheme.{0}}
    (j k : Q ⟶ W) (h : j = k)
    (s : SheafOfModules.unit W.ringCatSheaf ⟶ Conormal.idealModule j) :
    i1_module_sectionPullback j (Conormal.idealModule j) s ≫
        (eqToIso (congrArg Conormal.sheaf h)).hom =
      i1_module_sectionPullback k (Conormal.idealModule k)
        (s ≫ (eqToIso (congrArg Conormal.idealModule h)).hom) := by
  subst k
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]
  exact Category.comp_id _

/-- An equality of pullback maps preserves a normalized section. -/
theorem conormalSection_pullback_congr {X Y : Scheme.{0}}
    {f g : X ⟶ Y} (h : f = g) (M : Y.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    i1_module_sectionPullback f M s ≫ (Scheme.Modules.pullbackCongr h).hom.app M =
      i1_module_sectionPullback g M s := by
  subst g
  rfl

end HodgeLean.Foundations.TubularEuler
