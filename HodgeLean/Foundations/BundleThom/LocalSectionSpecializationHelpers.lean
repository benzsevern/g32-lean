import HodgeLean.Foundations.BundleThom.AnalyticNormalDefs

/-! # Specialization of local module sections

The actual point pullback and affine global-section functor are used throughout.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleThom

/-- Specialize a local section of an arbitrary module sheaf at its supplied complex point.
Source: Hartshorne, Algebraic Geometry, II.5, module sheaves and pullback. -/
def i1_localModuleSectionSpecialization {Q : Over (Spec ↧ℂ)} (M : Q.left.Modules)
    (U : Q.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj M)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf ⟶
      (Scheme.Modules.pullback x.left).obj M := by
  let a := ComplexPoint.liftToOpen Q U x hx
  letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
  exact
    inv (SheafOfModules.pullbackObjUnitToUnit a.toRingCatSheafHom) ≫
      (Scheme.Modules.pullback a).map s ≫
      (Scheme.Modules.pullbackComp a U.ι).hom.app M ≫
      (Scheme.Modules.pullbackCongr (ComplexPoint.liftToOpen_fac Q U x hx)).hom.app M
/-- The value of the specialized local module section.
Source: Hartshorne, Algebraic Geometry, II.5, specialization of sections. -/
def i1_localModuleSectionValue {Q : Over (Spec ↧ℂ)} (M : Q.left.Modules)
    (U : Q.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj M)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x.left).obj M) :=
  (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
    (i1_localModuleSectionSpecialization M U s x hx) (1 : Γ(Spec ↧ℂ, ⊤))

/-- Specializing a section commutes with the specified morphism of module sheaves.
Source: Hartshorne, Algebraic Geometry, II.5, functoriality of pullback and fibres. -/
theorem i1_localModuleSectionSpecialization_naturality {Q : Over (Spec ↧ℂ)}
    {M N : Q.left.Modules} (φ : M ⟶ N) (U : Q.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj M)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    i1_localModuleSectionSpecialization N U
      (s ≫ (Scheme.Modules.pullback U.ι).map φ) x hx =
      i1_localModuleSectionSpecialization M U s x hx ≫
        (Scheme.Modules.pullback x.left).map φ := by
  let a := ComplexPoint.liftToOpen Q U x hx
  letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
  let e := Scheme.Modules.pullbackComp a U.ι ≪≫
    Scheme.Modules.pullbackCongr (ComplexPoint.liftToOpen_fac Q U x hx)
  let w := inv (SheafOfModules.pullbackObjUnitToUnit a.toRingCatSheafHom)
  have hφ := e.hom.naturality φ
  change (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback U.ι).map φ) ≫
      e.hom.app N = e.hom.app M ≫ (Scheme.Modules.pullback x.left).map φ at hφ
  have ht : w ≫ (Scheme.Modules.pullback a).map
        (s ≫ (Scheme.Modules.pullback U.ι).map φ) ≫ e.hom.app N =
      (w ≫ (Scheme.Modules.pullback a).map s ≫ e.hom.app M) ≫
        (Scheme.Modules.pullback x.left).map φ := by
    calc
      _ = w ≫ ((Scheme.Modules.pullback a).map s ≫
          (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback U.ι).map φ)) ≫
          e.hom.app N := congrArg (fun z => w ≫ z ≫ e.hom.app N)
            ((Scheme.Modules.pullback a).map_comp s _)
      _ = w ≫ (Scheme.Modules.pullback a).map s ≫
          ((Scheme.Modules.pullback a).map ((Scheme.Modules.pullback U.ι).map φ) ≫
            e.hom.app N) := congrArg (fun z => w ≫ z) (Category.assoc _ _ _)
      _ = w ≫ (Scheme.Modules.pullback a).map s ≫
          (e.hom.app M ≫ (Scheme.Modules.pullback x.left).map φ) :=
            congrArg (fun z => w ≫ (Scheme.Modules.pullback a).map s ≫ z) hφ
      _ = _ := (congrArg (fun z => w ≫ z) (Category.assoc _ _ _).symm).trans
        (Category.assoc _ _ _).symm
  exact ht

/-- Specializing a section value commutes with the specified morphism of module sheaves.
Source: Hartshorne, Algebraic Geometry, II.5, functoriality of fibres. -/
theorem i1_localModuleSectionValue_naturality {Q : Over (Spec ↧ℂ)}
    {M N : Q.left.Modules} (φ : M ⟶ N) (U : Q.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj M)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    i1_localModuleSectionValue N U (s ≫ (Scheme.Modules.pullback U.ι).map φ) x hx =
      (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        ((Scheme.Modules.pullback x.left).map φ)
        (i1_localModuleSectionValue M U s x hx) := by
  let G := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  have h := congrArg (fun t => G.map t)
    (i1_localModuleSectionSpecialization_naturality φ U s x hx)
  have h' := h.trans (G.map_comp (i1_localModuleSectionSpecialization M U s x hx)
    ((Scheme.Modules.pullback x.left).map φ))
  have h'' := congrArg (fun t :
      G.obj (SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf) ⟶
        G.obj ((Scheme.Modules.pullback x.left).obj N) =>
      t.hom (1 : Γ(Spec ↧ℂ, ⊤))) h'
  exact h''

end HodgeLean.Foundations.BundleThom
