import HodgeLean.Foundations.BundleResolution.ModuleUnitPullbackHelpers

/-! # Coherence of actual section pullback and point specialization

The normalized unit comparison respects composition, and the supplied
local-section value is transport of actual point specialization.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Algebraic
namespace HodgeLean.Foundations.BundleResolution

theorem i1_module_unitPullback_comp_inv {X' X Y : Scheme.{0}}
    (a : X' ⟶ X) (f : X ⟶ Y) :
    (i1_module_unitPullbackIso (a ≫ f)).inv =
      (i1_module_unitPullbackIso a).inv ≫
        (Scheme.Modules.pullback a).map (i1_module_unitPullbackIso f).inv ≫
        (Scheme.Modules.pullbackComp a f).hom.app (SheafOfModules.unit Y.ringCatSheaf) := by
  let A := i1_module_unitPullbackIso a
  let B := i1_module_unitPullbackIso f
  let C := i1_module_unitPullbackIso (a ≫ f)
  let E := (Scheme.Modules.pullback a).mapIso B
  have hu : (Scheme.Modules.pullbackComp a f).hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫
      C.hom = E.hom ≫ A.hom := f5sheaf_pullbackComp_unit a f
  apply (cancel_mono C.hom).1
  change C.inv ≫ C.hom =
    (A.inv ≫ E.inv ≫ (Scheme.Modules.pullbackComp a f).hom.app
      (SheafOfModules.unit Y.ringCatSheaf)) ≫ C.hom
  simp only [Category.assoc, hu, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

theorem i1_module_sectionPullback_comp {X' X Y : Scheme.{0}}
    (a : X' ⟶ X) (f : X ⟶ Y) (M : Y.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    i1_module_sectionPullback (a ≫ f) M s =
      i1_module_sectionPullback a ((Scheme.Modules.pullback f).obj M)
        (i1_module_sectionPullback f M s) ≫ (Scheme.Modules.pullbackComp a f).hom.app M := by
  unfold i1_module_sectionPullback
  rw [i1_module_unitPullback_comp_inv]
  simp only [Functor.map_comp, Category.assoc]
  erw [(Scheme.Modules.pullbackComp a f).hom.naturality s]

def i1_module_pointValue {X : Scheme.{0}} (M : X.Modules)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ M) (a : Spec ↧ℂ ⟶ X) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj ((Scheme.Modules.pullback a).obj M) :=
  (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map (i1_module_sectionPullback a M s)
    (1 : Γ(Spec ↧ℂ, ⊤))

theorem i1_moduleSectionValue_pointValue {Q : Over (Spec ↧ℂ)}
    (M : Q.left.Modules) (U : Q.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶ (Scheme.Modules.pullback U.ι).obj M)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    i1_moduleSectionValue M U s x hx =
      (i1_module_openFibreIso M U x hx).hom
        (i1_module_pointValue ((Scheme.Modules.pullback U.ι).obj M) s
          (ComplexPoint.liftToOpen Q U x hx)) := by
  rfl
end HodgeLean.Foundations.BundleResolution
