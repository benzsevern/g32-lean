import HodgeLean.Foundations.Program.G32Native.PairedConormalPointSectionValues

/-! # Actual point-fibre comparison through the supplied module model -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.BundleThom

/-- The supplied module identification and literal equality of composed point
arrows determine the canonical isomorphism of actual complex fibres. -/
def pairedModelPointFibreIso {X Y Z : Scheme.{0}} (f : X ⟶ Y) (d : Z ⟶ Y)
    (C : X.Modules) (M : Y.Modules) (E : C ≅ (Scheme.Modules.pullback f).obj M)
    (x : Spec ↧ℂ ⟶ X) (z : Spec ↧ℂ ⟶ Z) (h : x ≫ f = z ≫ d) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj ((Scheme.Modules.pullback x).obj C) ≅
      (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
        ((Scheme.Modules.pullback z).obj ((Scheme.Modules.pullback d).obj M)) :=
  (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
    ((Scheme.Modules.pullback x).mapIso E ≪≫
      (Scheme.Modules.pullbackComp x f).app M ≪≫
      (Scheme.Modules.pullbackCongr h).app M ≪≫
      ((Scheme.Modules.pullbackComp z d).app M).symm)

/-- This actual point comparison retains the value of every supplied global
section, including its original pullback and module-identification maps. -/
theorem paired_modelPointFibre_value {X Y Z : Scheme.{0}} (f : X ⟶ Y) (d : Z ⟶ Y)
    (C : X.Modules) (M : Y.Modules) (E : C ≅ (Scheme.Modules.pullback f).obj M)
    (x : Spec ↧ℂ ⟶ X) (z : Spec ↧ℂ ⟶ Z) (h : x ≫ f = z ≫ d)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    (pairedModelPointFibreIso f d C M E x z h).hom
      (pairedPointSectionValue C (i1_moduleSectionPullback f M s ≫ E.inv) x) =
      pairedPointSectionValue ((Scheme.Modules.pullback d).obj M)
        (i1_moduleSectionPullback d M s) z := by
  let G := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  simp only [pairedModelPointFibreIso, Functor.mapIso_hom, Iso.trans_hom,
    Iso.symm_hom, Functor.map_comp, ModuleCat.comp_apply, Iso.app_hom, Iso.app_inv]
  rw [← paired_pointSectionValue_naturality E.hom
    (i1_moduleSectionPullback f M s ≫ E.inv) x,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let c := (Scheme.Modules.pullbackComp z d).app M
  let e := (Scheme.Modules.pullbackCongr h).app M
  have ha := congrArg (fun w : G.obj ((Scheme.Modules.pullback (x ≫ f)).obj M) =>
    G.map c.inv (G.map e.hom w)) (paired_pointSectionValue_pullback f M s x)
  have hb := congrArg (fun w : G.obj ((Scheme.Modules.pullback (z ≫ d)).obj M) =>
    G.map c.inv w) (paired_pointSectionValue_congr M s (x ≫ f) (z ≫ d) h)
  have hz := congrArg (fun w : G.obj ((Scheme.Modules.pullback (z ≫ d)).obj M) =>
    G.map c.inv w) (paired_pointSectionValue_pullback d M s z)
  have hc : G.map c.inv
      (G.map c.hom (pairedPointSectionValue ((Scheme.Modules.pullback d).obj M)
        (i1_moduleSectionPullback d M s) z)) =
      pairedPointSectionValue ((Scheme.Modules.pullback d).obj M)
        (i1_moduleSectionPullback d M s) z :=
    (G.mapIso c).toLinearEquiv.symm_apply_apply _
  exact ha.trans (hb.trans (hz.symm.trans hc))

/-- The dual point comparison retains evaluation of every supplied global
section after its original model pullback. -/
theorem paired_modelPointFibre_dual_value {X Y Z : Scheme.{0}} (f : X ⟶ Y) (d : Z ⟶ Y)
    (C : X.Modules) (M : Y.Modules) (E : C ≅ (Scheme.Modules.pullback f).obj M)
    (x : Spec ↧ℂ ⟶ X) (z : Spec ↧ℂ ⟶ Z) (h : x ≫ f = z ≫ d)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (ψ : Module.Dual ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x).obj C))) :
    (pairedModelPointFibreIso f d C M E x z h).toLinearEquiv.symm.dualMap ψ
      (pairedPointSectionValue ((Scheme.Modules.pullback d).obj M)
        (i1_moduleSectionPullback d M s) z) =
      ψ (pairedPointSectionValue C (i1_moduleSectionPullback f M s ≫ E.inv) x) := by
  change ψ ((pairedModelPointFibreIso f d C M E x z h).toLinearEquiv.symm _) = _
  apply congrArg ψ
  exact ((pairedModelPointFibreIso f d C M E x z h).toLinearEquiv.eq_symm_apply.mpr
    (paired_modelPointFibre_value f d C M E x z h s)).symm

#print axioms paired_modelPointFibre_dual_value
#print axioms pairedModelPointFibreIso
#print axioms paired_modelPointFibre_value
end HodgeLean.Foundations.Program.G32Native
