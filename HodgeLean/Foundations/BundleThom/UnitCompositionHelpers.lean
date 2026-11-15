import HodgeLean.Foundations.BundleThom.UnitSpecializationHelpers

/-! # Unit sheaf maps under composition of scheme morphisms

The unit maps keep the specified composite and canonical pushforward comparison.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleThom

/-- Canonical unit maps commute with composition of the actual scheme morphisms.
Source: Hartshorne, Algebraic Geometry, II.5, functoriality of pushforward module sheaves. -/
theorem i1_unitPushforward_composition {A B C : Scheme.{0}}
    (f : A ⟶ B) (g : B ⟶ C) :
    SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
      (Scheme.Modules.pushforward g).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app
        (SheafOfModules.unit.{0} A.ringCatSheaf) =
      SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom := by
  apply (SheafOfModules.unitHomEquiv _).injective
  ext V
  change (f.app (g ⁻¹ᵁ V.unop)) ((g.app V.unop) (1 : Γ(C, V.unop))) =
    ((f ≫ g).app V.unop) (1 : Γ(C, V.unop))
  rw [map_one (g.app V.unop).hom, map_one (f.app (g ⁻¹ᵁ V.unop)).hom,
    map_one ((f ≫ g).app V.unop).hom]

/-- Conjugate natural transformations respect the corresponding adjunction hom-set maps.
Source: Mac Lane, Categories for the Working Mathematician, IV.1, adjunction bijections. -/
theorem i1_conjugate_homEquiv {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {X : C} {Y : D} (h : L₁.obj X ⟶ Y) :
    adj₂.homEquiv X Y (α.app X ≫ h) =
      adj₁.homEquiv X Y h ≫ (conjugateEquiv adj₁ adj₂ α).app Y := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [← Category.assoc, ← unit_conjugateEquiv adj₁ adj₂ α X]
  rw [Category.assoc, ← (conjugateEquiv adj₁ adj₂ α).naturality h]

/-- Canonical unit pullbacks commute with the actual pullback-composition comparison.
Source: Hartshorne, Algebraic Geometry, II.5, composition of pullbacks of module sheaves. -/
theorem i1_unitPullback_composition {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) :
    letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
      (inferInstance : (Scheme.Modules.pushforward f).IsRightAdjoint)
    letI : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
      (inferInstance : (Scheme.Modules.pushforward g).IsRightAdjoint)
    letI : (SheafOfModules.pushforward (f ≫ g).toRingCatSheafHom).IsRightAdjoint :=
      (inferInstance : (Scheme.Modules.pushforward (f ≫ g)).IsRightAdjoint)
    (Scheme.Modules.pullback f).map
        (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) ≫
      SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom =
      (Scheme.Modules.pullbackComp f g).hom.app (SheafOfModules.unit.{0} C.ringCatSheaf) ≫
        SheafOfModules.pullbackObjUnitToUnit (f ≫ g).toRingCatSheafHom := by
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward f).IsRightAdjoint)
  letI : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward g).IsRightAdjoint)
  letI : (SheafOfModules.pushforward (f ≫ g).toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward (f ≫ g)).IsRightAdjoint)
  let UA := SheafOfModules.unit.{0} A.ringCatSheaf
  let UB := SheafOfModules.unit.{0} B.ringCatSheaf
  let UC := SheafOfModules.unit.{0} C.ringCatSheaf
  let df := Scheme.Modules.pullbackPushforwardAdjunction f
  let dg := Scheme.Modules.pullbackPushforwardAdjunction g
  let dc := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  let uf : (Scheme.Modules.pullback f).obj UB ⟶ UA :=
    SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  let ug : (Scheme.Modules.pullback g).obj UC ⟶ UB :=
    SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom
  let uc : (Scheme.Modules.pullback (f ≫ g)).obj UC ⟶ UA :=
    SheafOfModules.pullbackObjUnitToUnit (f ≫ g).toRingCatSheafHom
  let vf := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let vg := SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom
  let vc := SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom
  let e := Scheme.Modules.pullbackComp f g
  let h := (Scheme.Modules.pullback f).map ug ≫ uf
  have hf : df.homEquiv UB UA uf = vf :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hg : dg.homEquiv UC UB ug = vg :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hc : dc.homEquiv UC UA uc = vc :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hi : df.homEquiv _ UA h = ug ≫ vf :=
    (df.homEquiv_naturality_left ug uf).trans (congrArg (fun z => ug ≫ z) hf)
  have hj : dg.homEquiv UC _ (ug ≫ vf) = vg ≫ (Scheme.Modules.pushforward g).map vf :=
    (dg.homEquiv_naturality_right ug vf).trans
      (congrArg (fun z => z ≫ (Scheme.Modules.pushforward g).map vf) hg)
  have hd : (dg.comp df).homEquiv UC UA h =
      vg ≫ (Scheme.Modules.pushforward g).map vf := by
    have hi' := (congrArg (dg.homEquiv UC ((Scheme.Modules.pushforward f).obj UA)) hi).trans hj
    have he := congrArg (fun q => q UC UA h) (Adjunction.comp_homEquiv dg df)
    exact he.trans hi'
  have hm := i1_conjugate_homEquiv (dg.comp df) dc e.inv h
  have hm' : dc.homEquiv UC UA (e.inv.app UC ≫ h) =
      (dg.comp df).homEquiv UC UA h ≫ (Scheme.Modules.pushforwardComp f g).hom.app UA :=
    hm.trans (congrArg (fun z :
      Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g ⟶
        Scheme.Modules.pushforward (f ≫ g) =>
      (dg.comp df).homEquiv UC UA h ≫ z.app UA)
        (Scheme.Modules.conjugateEquiv_pullbackComp_inv f g))
  have hz : dc.homEquiv UC UA (e.inv.app UC ≫ h) = vc :=
    hm'.trans ((congrArg (fun z => z ≫ (Scheme.Modules.pushforwardComp f g).hom.app UA) hd).trans
      ((Category.assoc _ _ _).trans (i1_unitPushforward_composition f g)))
  have heq : e.inv.app UC ≫ h = uc := (dc.homEquiv UC UA).injective (hz.trans hc.symm)
  have heq' := congrArg (fun z => e.hom.app UC ≫ z) heq
  have hreduce : e.hom.app UC ≫ e.inv.app UC ≫ h = h :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ h) (e.app UC).hom_inv_id).trans (Category.id_comp _))
  exact hreduce.symm.trans heq'

end HodgeLean.Foundations.BundleThom
