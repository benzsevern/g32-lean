import HodgeLean.Foundations.BundleThom.AnalyticNormalFramesHelpers
import HodgeLean.Foundations.BundleThom.LocalSectionSpecializationHelpers

/-! # Actual local sections of a conormal frame

The local sections retain the specified free-sheaf comparison.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleThom

/-- The actual local section corresponding to the specified frame index.
Source: Hartshorne, Algebraic Geometry, II.5, local frames of a locally free sheaf. -/
def i1_conormalFrameSection {Q : Over (Spec ↧ℂ)} {V : Scheme}
    (j : Q.left ⟶ V) (k : ℕ) (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k))) (i : Fin k) :
    SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) :=
  SheafOfModules.ιFree i ≫ E.inv

/-- The specified local frame sections specialize to the standard free-sheaf generators.
Source: Hartshorne, Algebraic Geometry, II.5, pullback of local frames. -/
theorem i1_conormalFrameSection_specialization {Q : Over (Spec ↧ℂ)} {V : Scheme}
    (j : Q.left ⟶ V) (k : ℕ) (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k)))
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) (i : Fin k) :
    i1_localModuleSectionSpecialization (Conormal.sheaf j) U
      (i1_conormalFrameSection j k U E i) x hx ≫
        (i1_conormalFramePointIso j k U E x hx).hom =
      SheafOfModules.ιFree (R := (Spec ↧ℂ).ringCatSheaf) i := by
  let a := ComplexPoint.liftToOpen Q U x hx
  letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
  let F := Scheme.Modules.pullback a
  let K := Scheme.Modules.pullbackComp a U.ι ≪≫
    Scheme.Modules.pullbackCongr (ComplexPoint.liftToOpen_fac Q U x hx)
  let u := SheafOfModules.pullbackObjUnitToUnit a.toRingCatSheafHom
  let p := SheafOfModules.pullbackObjFreeIso a.toRingCatSheafHom (Fin k)
  change (inv u ≫ F.map (SheafOfModules.ιFree i ≫ E.inv) ≫ K.hom.app _) ≫
    (K.inv.app _ ≫ F.map E.hom ≫ p.hom) = _
  have hc : F.map E.inv ≫ F.map E.hom = 𝟙 _ := (F.mapIso E).inv_hom_id
  have hc' := Category.assoc (F.map E.inv) (F.map E.hom) p.hom
  have hcancel : F.map E.inv ≫ F.map E.hom ≫ p.hom = p.hom :=
    hc'.symm.trans ((congrArg (fun z => z ≫ p.hom) hc).trans (Category.id_comp _))
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [hcancel]
  change inv u ≫ F.map (SheafOfModules.ιFree i) ≫ p.hom = _
  have hfree : F.map (SheafOfModules.ιFree i) ≫ p.hom =
      u ≫ SheafOfModules.ιFree i :=
    SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom
      (φ := a.toRingCatSheafHom) i
  exact (congrArg (fun z => inv u ≫ z) hfree).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ SheafOfModules.ιFree i) (IsIso.inv_hom_id u)).trans
        (Category.id_comp _)))

/-- Specialized frame section values become the standard free-sheaf section values.
Source: Hartshorne, Algebraic Geometry, II.5, fibres of local frames. -/
theorem i1_conormalFrameSection_value {Q : Over (Spec ↧ℂ)} {V : Scheme}
    (j : Q.left ⟶ V) (k : ℕ) (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k)))
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) (i : Fin k) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      (i1_conormalFramePointIso j k U E x hx).hom
        (i1_conormalSectionValue j U (i1_conormalFrameSection j k U E i) x hx) =
      (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        (SheafOfModules.ιFree (R := (Spec ↧ℂ).ringCatSheaf) i)
          (1 : Γ(Spec ↧ℂ, ⊤)) := by
  let G := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  let t := i1_localModuleSectionSpecialization (Conormal.sheaf j) U
    (i1_conormalFrameSection j k U E i) x hx
  have h := congrArg (fun z => G.map z)
    (i1_conormalFrameSection_specialization j k U E x hx i)
  have h' := (G.map_comp t (i1_conormalFramePointIso j k U E x hx).hom).symm.trans h
  exact congrArg (fun z :
      G.obj (SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf) ⟶
        G.obj (SheafOfModules.free (R := (Spec ↧ℂ).ringCatSheaf) (Fin k)) =>
      z.hom (1 : Γ(Spec ↧ℂ, ⊤))) h'

/-- The actual frame section values have the standard coordinate vectors.
Source: Hartshorne, Algebraic Geometry, II.5, coordinate vectors of a local frame. -/
theorem i1_conormalFrameCoordinates_frameSection {Q : Over (Spec ↧ℂ)} {V : Scheme}
    (j : Q.left ⟶ V) (k : ℕ) (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k)))
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) (i : Fin k) :
    i1_conormalFrameCoordinates j k U E x hx
      (i1_conormalSectionValue j U (i1_conormalFrameSection j k U E i) x hx) =
      Pi.single i 1 := by
  let G := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  have hv := congrArg (i1_freePointCoordinates k)
    (i1_conormalFrameSection_value j k U E x hx i)
  have hu := congrArg (fun v : G.obj (SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf) =>
      i1_freePointCoordinates k (G.map (SheafOfModules.ιFree i) v))
    i1_pointUnitComparison_one
  exact hv.trans (hu.symm.trans (i1_freePointCoordinates_generator k i))

/-- The conormal fibre basis selected by the specified actual local frame.
Source: Hartshorne, Algebraic Geometry, II.5, fibres of locally free sheaves. -/
def i1_conormalFrameBasis {Q : Over (Spec ↧ℂ)} {V : Scheme}
    (j : Q.left ⟶ V) (k : ℕ) (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k)))
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    Module.Basis (Fin k) ℂ (i1_conormalFibre j x) :=
  Module.Basis.ofEquivFun (i1_conormalFrameCoordinates j k U E x hx)

/-- The fibre basis consists of the specializations of the actual frame sections.
Source: Hartshorne, Algebraic Geometry, II.5, local frames and fibres. -/
theorem i1_conormalFrameBasis_apply {Q : Over (Spec ↧ℂ)} {V : Scheme}
    (j : Q.left ⟶ V) (k : ℕ) (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k)))
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) (i : Fin k) :
    i1_conormalFrameBasis j k U E x hx i =
      i1_conormalSectionValue j U (i1_conormalFrameSection j k U E i) x hx := by
  let e := i1_conormalFrameCoordinates j k U E x hx
  have hb := congrFun (Module.Basis.coe_ofEquivFun e) i
  have hv := congrArg e.symm
    (i1_conormalFrameCoordinates_frameSection j k U E x hx i)
  exact hb.trans (hv.symm.trans (LinearEquiv.symm_apply_apply _ _))

end HodgeLean.Foundations.BundleThom
