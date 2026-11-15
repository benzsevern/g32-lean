import HodgeLean.Foundations.Program.G32Native.ConormalIdealAmbientNaturality
import HodgeLean.Foundations.BundleResolution.ModulePointValueAlgebraHelpers

/-! # Ideal sections through the original ambient comparison -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program HodgeLean.Foundations.BundleResolution
open HodgeLean.Foundations.Algebraic

/-- An ideal section is determined by its structure-module inclusion. -/
theorem idealSection_ext {Q W : Scheme.{0}} (j : Q ⟶ W)
    (s t : SheafOfModules.unit W.ringCatSheaf ⟶ Conormal.idealModule j)
    (h : s ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) =
      t ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)) : s = t :=
  (cancel_mono (kernel.ι (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom))).1 h

/-- Pullback through the ambient comparison retains the specified regular function. -/
theorem idealSection_ambient_pullback {Q W W' : Scheme.{0}}
    (j : Q ⟶ W) (e : W ≅ W')
    (s : SheafOfModules.unit W.ringCatSheaf ⟶ Conormal.idealModule j)
    (t : SheafOfModules.unit W'.ringCatSheaf ⟶ Conormal.idealModule (j ≫ e.hom))
    (c : Γ(W', ⊤))
    (hs : s ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) =
      f5sheaf_scal (e.hom.appTop c))
    (ht : t ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (j ≫ e.hom).toRingCatSheafHom) = f5sheaf_scal c) :
    i1_module_sectionPullback e.hom (Conormal.idealModule (j ≫ e.hom)) t ≫
      (conormalChartAmbientIdealIso j e).hom = s := by
  apply idealSection_ext j
  rw [Category.assoc, conormalChartAmbientIdealIso_inclusion]
  unfold i1_module_sectionPullback
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, ht]
  change (i1_module_unitPullbackIso e.hom).inv ≫
    (Scheme.Modules.pullback e.hom).map (f5sheaf_scal c) ≫
      (i1_module_unitPullbackIso e.hom).hom = _
  have hp : (Scheme.Modules.pullback e.hom).map (f5sheaf_scal c) ≫
      (i1_module_unitPullbackIso e.hom).hom =
        (i1_module_unitPullbackIso e.hom).hom ≫ f5sheaf_scal (e.hom.appTop c) :=
    f5sheaf_pullback_scal e.hom c
  rw [hp, Iso.inv_hom_id_assoc, hs]

end HodgeLean.Foundations.TubularEuler
