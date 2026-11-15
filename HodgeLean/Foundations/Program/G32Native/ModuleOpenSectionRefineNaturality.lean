import HodgeLean.Foundations.Program.G32Native.ModuleRestrictionPullbackNaturality
import HodgeLean.Foundations.Program.G32Native.OriginalModuleOpenSectionNaturality
import HodgeLean.Foundations.Program.G32Native.ConormalSectionIsoNaturality

/-! # Normalized module sections on nested open subsets -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution HodgeLean.Foundations.Algebraic

/-- The original value on an open as a section of the actual pullback module. -/
def moduleOpenSectionPullbackOfValue {W : Scheme.{0}} (M : W.Modules)
    (A : W.Opens) (t : Γ(M, A)) :
    SheafOfModules.unit.{0} A.toScheme.ringCatSheaf ⟶ (Scheme.Modules.pullback A.ι).obj M :=
  moduleOpenSectionOfValue M A t ≫ (Scheme.Modules.restrictFunctorIsoPullback A.ι).hom.app M

/-- Normalized pullback along an open immersion is normalized restriction. -/
theorem moduleSectionPullback_eq_restrict {X Y : Scheme.{0}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    (s : SheafOfModules.unit.{0} Y.ringCatSheaf ⟶ M) :
    i1_module_sectionPullback f M s =
      (Scheme.Modules.restrictUnitIso f).inv ≫
        (Scheme.Modules.restrictFunctor f).map s ≫
          (Scheme.Modules.restrictFunctorIsoPullback f).hom.app M := by
  have hunit : (Scheme.Modules.restrictFunctorIsoPullback f).hom.app
      (SheafOfModules.unit.{0} Y.ringCatSheaf) ≫
        (i1_module_unitPullbackIso f).hom = (Scheme.Modules.restrictUnitIso f).hom :=
    f5sheaf_restrictIsoPullback_unit f
  have hu : (Scheme.Modules.restrictUnitIso f).inv ≫
      (Scheme.Modules.restrictFunctorIsoPullback f).hom.app
        (SheafOfModules.unit.{0} Y.ringCatSheaf) = (i1_module_unitPullbackIso f).inv := by
    apply (cancel_mono (i1_module_unitPullbackIso f).hom).1
    rw [Category.assoc, hunit, Iso.inv_hom_id, Iso.inv_hom_id]
  dsimp only [i1_module_sectionPullback]
  rw [← hu, Category.assoc, ← (Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality s]

/-- The restriction/pullback comparison respects nested original opens. -/
theorem moduleRestrictionPullback_nest {W : Scheme.{0}} (M : W.Modules)
    {A B : W.Opens} (h : B ≤ A) :
    (f5sheaf_restrictNest h).hom.app M ≫
      (Scheme.Modules.restrictFunctor (W.homOfLE h)).map
        ((Scheme.Modules.restrictFunctorIsoPullback A.ι).hom.app M) ≫
      (Scheme.Modules.restrictFunctorIsoPullback (W.homOfLE h)).hom.app
        ((Scheme.Modules.pullback A.ι).obj M) ≫
      (Scheme.Modules.pullbackComp (W.homOfLE h) A.ι).hom.app M ≫
      (Scheme.Modules.pullbackCongr (W.homOfLE_ι h)).hom.app M =
        (Scheme.Modules.restrictFunctorIsoPullback B.ι).hom.app M := by
  let b := W.homOfLE h
  have hc := congr_app (moduleRestrictionPullback_comp b A.ι) M
  dsimp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] at hc
  have hc' := (Iso.comp_inv_eq ((Scheme.Modules.pullbackComp b A.ι).app M)).mp hc
  simp only [Category.assoc] at hc'
  have hn := congr_app (moduleRestrictionPullback_congr (b ≫ A.ι) B.ι (W.homOfLE_ι h)) M
  dsimp only [NatTrans.comp_app] at hn
  have he := congr_app (moduleRestrictionCongr_symm_comp (b ≫ A.ι) B.ι (W.homOfLE_ι h)) M
  dsimp only [NatTrans.comp_app, NatTrans.id_app] at he
  dsimp only [f5sheaf_restrictNest, Iso.trans_hom, NatTrans.comp_app]
  simp only [Category.assoc]
  erw [← reassoc_of% hc', ← hn, ← Category.assoc, he, Category.id_comp]

/-- Refinement of an original normalized section is the normalized restricted value. -/
theorem moduleOpenSectionPullbackOfValue_refine {W : Scheme.{0}} (M : W.Modules)
    {A B : W.Opens} (h : B ≤ A) (t : Γ(M, A)) :
    i1_module_sectionPullback (W.homOfLE h) ((Scheme.Modules.pullback A.ι).obj M)
        (moduleOpenSectionPullbackOfValue M A t) ≫
      (Scheme.Modules.pullbackComp (W.homOfLE h) A.ι).hom.app M ≫
      (Scheme.Modules.pullbackCongr (W.homOfLE_ι h)).hom.app M =
        moduleOpenSectionPullbackOfValue M B (M.presheaf.map (homOfLE h).op t) := by
  dsimp only [moduleOpenSectionPullbackOfValue]
  rw [conormalSection_pullback_map,
    moduleSectionPullback_eq_restrict (W.homOfLE h)]
  simp only [Category.assoc]
  have hn := ((Scheme.Modules.restrictFunctorIsoPullback (W.homOfLE h)).hom.naturality
    ((Scheme.Modules.restrictFunctorIsoPullback A.ι).hom.app M)).symm
  rw [reassoc_of% hn]
  rw [← reassoc_of% (moduleOpenSectionOfValue_restrict M h t)]
  rw [moduleRestrictionPullback_nest M h]

end HodgeLean.Foundations.TubularEuler
