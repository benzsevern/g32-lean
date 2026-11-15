import HodgeLean.Foundations.BundleThom.UnitCompositionHelpers

/-! # Canonical pullback of module sections

The unit comparison records how actual section morphisms pull back under composition.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleThom

/-- Pull back an actual module section using the canonical unit comparison.
Source: Hartshorne, Algebraic Geometry, II.5, pullback of module sections. -/
def i1_moduleSectionPullback {A B : Scheme.{0}} (f : A ⟶ B) (M : B.Modules)
    (s : SheafOfModules.unit.{0} B.ringCatSheaf ⟶ M) :
    SheafOfModules.unit.{0} A.ringCatSheaf ⟶ (Scheme.Modules.pullback f).obj M := by
  letI : (TopologicalSpace.Opens.map f.base).Final := inferInstance
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward f).IsRightAdjoint)
  let u : (Scheme.Modules.pullback f).obj (SheafOfModules.unit.{0} B.ringCatSheaf) ⟶
      SheafOfModules.unit.{0} A.ringCatSheaf :=
    SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  letI : IsIso u := inferInstanceAs (IsIso
    (SheafOfModules.pullbackObjUnitToUnit (F := TopologicalSpace.Opens.map f.base)
      f.toRingCatSheafHom))
  exact inv u ≫ (Scheme.Modules.pullback f).map s

/-- The actual canonical unit comparison as an isomorphism of module sheaves.
Source: Hartshorne, Algebraic Geometry, II.5, pullback of the unit module. -/
def i1_unitPullbackIso {A B : Scheme.{0}} (f : A ⟶ B) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit.{0} B.ringCatSheaf) ≅
      SheafOfModules.unit.{0} A.ringCatSheaf := by
  letI : (TopologicalSpace.Opens.map f.base).Final := inferInstance
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward f).IsRightAdjoint)
  let u : (Scheme.Modules.pullback f).obj (SheafOfModules.unit.{0} B.ringCatSheaf) ⟶
      SheafOfModules.unit.{0} A.ringCatSheaf :=
    SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  letI : IsIso u := inferInstanceAs (IsIso
    (SheafOfModules.pullbackObjUnitToUnit (F := TopologicalSpace.Opens.map f.base)
      f.toRingCatSheafHom))
  exact asIso u

/-- Inverse canonical unit comparisons commute with the actual composite pullback.
Source: Hartshorne, Algebraic Geometry, II.5, composition of pullbacks of the unit module. -/
theorem i1_unitPullbackIso_inverse_composition {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) :
    (i1_unitPullbackIso f).inv ≫ (Scheme.Modules.pullback f).map (i1_unitPullbackIso g).inv ≫
      (Scheme.Modules.pullbackComp f g).hom.app (SheafOfModules.unit.{0} C.ringCatSheaf) =
      (i1_unitPullbackIso (f ≫ g)).inv := by
  let F := Scheme.Modules.pullback f
  let uf := i1_unitPullbackIso f
  let ug := i1_unitPullbackIso g
  let uc := i1_unitPullbackIso (f ≫ g)
  let e := Scheme.Modules.pullbackComp f g
  let U := SheafOfModules.unit.{0} C.ringCatSheaf
  have hu : F.map ug.hom ≫ uf.hom = e.hom.app U ≫ uc.hom :=
    i1_unitPullback_composition f g
  have hm : F.map ug.inv ≫ F.map ug.hom = 𝟙 _ := (F.mapIso ug).inv_hom_id
  apply (cancel_mono uc.hom).mp
  calc
    (uf.inv ≫ F.map ug.inv ≫ e.hom.app U) ≫ uc.hom =
        uf.inv ≫ F.map ug.inv ≫ (e.hom.app U ≫ uc.hom) := by
      simp only [Category.assoc]
    _ = uf.inv ≫ F.map ug.inv ≫ (F.map ug.hom ≫ uf.hom) :=
      congrArg (fun z => uf.inv ≫ F.map ug.inv ≫ z) hu.symm
    _ = uf.inv ≫ (F.map ug.inv ≫ F.map ug.hom) ≫ uf.hom :=
      congrArg (fun z => uf.inv ≫ z) (Category.assoc _ _ _).symm
    _ = uf.inv ≫ uf.hom :=
      (congrArg (fun z => uf.inv ≫ z ≫ uf.hom) hm).trans
        (congrArg (fun z => uf.inv ≫ z) (Category.id_comp _))
    _ = 𝟙 _ := uf.inv_hom_id
    _ = uc.inv ≫ uc.hom := uc.inv_hom_id.symm

/-- Canonical section pullback commutes with the specified module-sheaf morphism.
Source: Hartshorne, Algebraic Geometry, II.5, functoriality of module-section pullback. -/
theorem i1_moduleSectionPullback_naturality {A B : Scheme.{0}} (f : A ⟶ B)
    {M N : B.Modules} (φ : M ⟶ N) (s : SheafOfModules.unit.{0} B.ringCatSheaf ⟶ M) :
    i1_moduleSectionPullback f N (s ≫ φ) =
      i1_moduleSectionPullback f M s ≫ (Scheme.Modules.pullback f).map φ := by
  let F := Scheme.Modules.pullback f
  let u := i1_unitPullbackIso f
  change u.inv ≫ F.map (s ≫ φ) = (u.inv ≫ F.map s) ≫ F.map φ
  exact (congrArg (fun z => u.inv ≫ z) (F.map_comp s φ)).trans (Category.assoc _ _ _).symm

/-- Canonical module-section pullback commutes with the actual pullback-composition comparison.
Source: Hartshorne, Algebraic Geometry, II.5, composition of pullbacks of module sections. -/
theorem i1_moduleSectionPullback_composition {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C)
    (M : C.Modules) (s : SheafOfModules.unit.{0} C.ringCatSheaf ⟶ M) :
    i1_moduleSectionPullback f ((Scheme.Modules.pullback g).obj M)
        (i1_moduleSectionPullback g M s) ≫
      (Scheme.Modules.pullbackComp f g).hom.app M =
      i1_moduleSectionPullback (f ≫ g) M s := by
  let F := Scheme.Modules.pullback f
  let G := Scheme.Modules.pullback g
  let H := Scheme.Modules.pullback (f ≫ g)
  let uf := i1_unitPullbackIso f
  let ug := i1_unitPullbackIso g
  let uc := i1_unitPullbackIso (f ≫ g)
  let e := Scheme.Modules.pullbackComp f g
  let U := SheafOfModules.unit.{0} C.ringCatSheaf
  have hn := e.hom.naturality s
  change F.map (G.map s) ≫ e.hom.app M = e.hom.app U ≫ H.map s at hn
  have hi : uf.inv ≫ F.map ug.inv ≫ e.hom.app U = uc.inv :=
    i1_unitPullbackIso_inverse_composition f g
  change (uf.inv ≫ F.map (ug.inv ≫ G.map s)) ≫ e.hom.app M = uc.inv ≫ H.map s
  calc
    _ = (uf.inv ≫ (F.map ug.inv ≫ F.map (G.map s))) ≫ e.hom.app M :=
      congrArg (fun z => (uf.inv ≫ z) ≫ e.hom.app M) (F.map_comp ug.inv (G.map s))
    _ = uf.inv ≫ F.map ug.inv ≫ (F.map (G.map s) ≫ e.hom.app M) := by
      simp only [Category.assoc]
    _ = uf.inv ≫ F.map ug.inv ≫ (e.hom.app U ≫ H.map s) :=
      congrArg (fun z => uf.inv ≫ F.map ug.inv ≫ z) hn
    _ = (uf.inv ≫ F.map ug.inv ≫ e.hom.app U) ≫ H.map s := by
      simp only [Category.assoc]
    _ = uc.inv ≫ H.map s := congrArg (fun z => z ≫ H.map s) hi

end HodgeLean.Foundations.BundleThom
