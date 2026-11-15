import HodgeLean.Foundations.BundleThom.FrameSectionsHelpers
import HodgeLean.Foundations.BundleThom.LocalSectionRestrictionHelpers

/-! # Restriction of actual conormal frames

The restricted frame retains the specified frame and canonical comparison maps.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleThom

/-- Restrict the supplied actual conormal frame to the specified smaller scheme open.
Source: Hartshorne, Algebraic Geometry, II.5, restriction of finite free module frames. -/
def i1_conormalFrameRestriction {Q : Over (Spec ↧ℂ)} {W : Scheme}
    (j : Q.left ⟶ W) (k : ℕ) {U V : Q.left.Opens} (hVU : V ≤ U)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k)) :
    (Scheme.Modules.pullback V.ι).obj (Conormal.sheaf j) ≅
      SheafOfModules.free.{0} (R := V.toScheme.ringCatSheaf) (Fin k) := by
  let a := Q.left.homOfLE hVU
  letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
  exact ((Scheme.Modules.pullbackComp a U.ι ≪≫
      Scheme.Modules.pullbackCongr (Q.left.homOfLE_ι hVU)).symm.app _) ≪≫
    (Scheme.Modules.pullback a).mapIso E ≪≫
      SheafOfModules.pullbackObjFreeIso a.toRingCatSheafHom (Fin k)

/-- Restricting each actual frame section gives the corresponding section of the restricted frame.
Source: Hartshorne, Algebraic Geometry, II.5, restriction of local frames. -/
theorem i1_conormalFrameSection_restriction {Q : Over (Spec ↧ℂ)} {W : Scheme}
    (j : Q.left ⟶ W) (k : ℕ) {U V : Q.left.Opens} (hVU : V ≤ U)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k)) (i : Fin k) :
    i1_localModuleSectionRestriction (Conormal.sheaf j) hVU (i1_conormalFrameSection j k U E i) =
      i1_conormalFrameSection j k V (i1_conormalFrameRestriction j k hVU E) i := by
  let a := Q.left.homOfLE hVU
  letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
  let F := Scheme.Modules.pullback a
  let K := Scheme.Modules.pullbackComp a U.ι ≪≫
    Scheme.Modules.pullbackCongr (Q.left.homOfLE_ι hVU)
  let u := i1_unitPullbackIso a
  let p := SheafOfModules.pullbackObjFreeIso a.toRingCatSheafHom (Fin k)
  let e := i1_conormalFrameRestriction j k hVU E
  apply (cancel_mono e.hom).mp
  have hl : i1_localModuleSectionRestriction (Conormal.sheaf j) hVU
      (i1_conormalFrameSection j k U E i) ≫ e.hom =
      SheafOfModules.ιFree (R := V.toScheme.ringCatSheaf) i := by
    change ((u.inv ≫ F.map (SheafOfModules.ιFree i ≫ E.inv)) ≫ K.hom.app _) ≫
      (K.inv.app _ ≫ F.map E.hom ≫ p.hom) = _
    have hc : F.map E.inv ≫ F.map E.hom = 𝟙 _ := (F.mapIso E).inv_hom_id
    have hcancel : F.map E.inv ≫ F.map E.hom ≫ p.hom = p.hom :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ p.hom) hc).trans (Category.id_comp _))
    simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [hcancel]
    have hfree : F.map (SheafOfModules.ιFree i) ≫ p.hom =
        u.hom ≫ SheafOfModules.ιFree i :=
      SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom
        (φ := a.toRingCatSheafHom) i
    exact (congrArg (fun z => u.inv ≫ z) hfree).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ SheafOfModules.ιFree i) u.inv_hom_id).trans
          (Category.id_comp _)))
  have hr : i1_conormalFrameSection j k V e i ≫ e.hom =
      SheafOfModules.ιFree (R := V.toScheme.ringCatSheaf) i :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => SheafOfModules.ιFree i ≫ z) e.inv_hom_id).trans (Category.comp_id _))
  exact hl.trans hr.symm

/-- The restricted actual frame gives the original conormal fibre basis at the supplied point.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8, restriction of conormal frames. -/
theorem i1_conormalFrameBasis_restriction {Q : Over (Spec ↧ℂ)} {W : Scheme}
    (j : Q.left ⟶ W) (k : ℕ) {U V : Q.left.Opens} (hVU : V ≤ U)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (x : ComplexPoint Q) (hxV : x ∈ Point.overOpen V) :
    i1_conormalFrameBasis j k V (i1_conormalFrameRestriction j k hVU E) x hxV =
      i1_conormalFrameBasis j k U E x (hVU hxV) := by
  apply DFunLike.ext
  intro i
  exact (i1_conormalFrameBasis_apply j k V (i1_conormalFrameRestriction j k hVU E) x hxV i).trans
    ((congrArg (fun s => i1_conormalSectionValue j V s x hxV)
      (i1_conormalFrameSection_restriction j k hVU E i).symm).trans
      ((i1_conormalSectionValue_restriction j hVU (i1_conormalFrameSection j k U E i) x hxV).trans
        (i1_conormalFrameBasis_apply j k U E x (hVU hxV) i).symm))

end HodgeLean.Foundations.BundleThom
