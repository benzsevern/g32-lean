import HodgeLean.Foundations.BundleThom.FrameSectionsHelpers
import HodgeLean.Foundations.BundleThom.FreeSectionSpecializationHelpers

/-! # Regular coefficients in the actual local conormal frame

Arbitrary algebraic sections retain the specified frame isomorphism and point.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleThom

/-- Actual local frame transport commutes with specialization of every conormal section.
Source: Hartshorne, Algebraic Geometry, II.5, local frames and pullback of sections. -/
theorem i1_conormalFrame_specialization {Q : Over (Spec ↧ℂ)} {V : Scheme}
    (j : Q.left ⟶ V) (k : ℕ) (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (s : SheafOfModules.unit.{0} U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j))
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    i1_localModuleSectionSpecialization (Conormal.sheaf j) U s x hx ≫
        (i1_conormalFramePointIso j k U E x hx).hom =
      i1_freeSectionSpecialization (ComplexPoint.openScheme Q U) k (s ≫ E.hom)
        (ComplexPoint.asOpenPoint Q U x hx) := by
  let a := ComplexPoint.liftToOpen Q U x hx
  letI : (TopologicalSpace.Opens.map a.base).Final := inferInstance
  letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
  let F := Scheme.Modules.pullback a
  let u : F.obj (SheafOfModules.unit.{0} U.toScheme.ringCatSheaf) ⟶
      SheafOfModules.unit.{0} (Spec ↧ℂ).ringCatSheaf :=
    SheafOfModules.pullbackObjUnitToUnit a.toRingCatSheafHom
  letI : IsIso u := inferInstanceAs (IsIso
    (SheafOfModules.pullbackObjUnitToUnit (F := TopologicalSpace.Opens.map a.base)
      a.toRingCatSheafHom))
  let K := Scheme.Modules.pullbackComp a U.ι ≪≫
    Scheme.Modules.pullbackCongr (ComplexPoint.liftToOpen_fac Q U x hx)
  let p := SheafOfModules.pullbackObjFreeIso a.toRingCatSheafHom (Fin k)
  change (inv u ≫ F.map s ≫ K.hom.app _) ≫
      (K.inv.app _ ≫ F.map E.hom ≫ p.hom) =
    inv u ≫ F.map (s ≫ E.hom) ≫ p.hom
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  exact (congrArg (fun z => inv u ≫ z) (Category.assoc _ _ _).symm).trans
    (congrArg (fun z => inv u ≫ z ≫ p.hom) (F.map_comp s E.hom).symm)

/-- The actual conormal frame coordinates of a section are its free-section specialization.
Source: Hartshorne, Algebraic Geometry, II.5, coefficients of local frames. -/
theorem i1_conormalFrameCoordinates_sectionValue {Q : Over (Spec ↧ℂ)} {V : Scheme}
    (j : Q.left ⟶ V) (k : ℕ) (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (s : SheafOfModules.unit.{0} U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j))
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    i1_conormalFrameCoordinates j k U E x hx (i1_conormalSectionValue j U s x hx) =
      i1_freePointCoordinates k
        ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
          (i1_freeSectionSpecialization (ComplexPoint.openScheme Q U) k (s ≫ E.hom)
            (ComplexPoint.asOpenPoint Q U x hx)) (1 : Γ(Spec ↧ℂ, ⊤))) := by
  let G := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  let t := i1_localModuleSectionSpecialization (Conormal.sheaf j) U s x hx
  have hm := (G.map_comp t (i1_conormalFramePointIso j k U E x hx).hom).symm.trans
    (congrArg (fun z => G.map z) (i1_conormalFrame_specialization j k U E s x hx))
  have hv := congrArg (fun z : G.obj (SheafOfModules.unit.{0} (Spec ↧ℂ).ringCatSheaf) ⟶
      G.obj (SheafOfModules.free.{0} (R := (Spec ↧ℂ).ringCatSheaf) (Fin k)) =>
      z.hom (1 : Γ(Spec ↧ℂ, ⊤))) hm
  exact congrArg (i1_freePointCoordinates k) hv

/-- Coefficients of an arbitrary conormal section in the specified actual frame are continuous.
Source: Hartshorne, Algebraic Geometry, II.5, analytification of local frame coefficients. -/
theorem i1_conormalFrameCoordinates_section_continuous {Q : Over (Spec ↧ℂ)} {V : Scheme}
    (j : Q.left ⟶ V) (k : ℕ) (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (s : SheafOfModules.unit.{0} U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j)) :
    Continuous (fun x : ↥(Point.overOpen U : Set (ComplexPoint Q)) =>
      i1_conormalFrameCoordinates j k U E x.1 x.2 (i1_conormalSectionValue j U s x.1 x.2)) := by
  have ho : Continuous (fun x : ↥(Point.overOpen U : Set (ComplexPoint Q)) =>
      ComplexPoint.asOpenPoint Q U x.1 x.2) :=
    ComplexPoint.continuous_openEquiv_symm Q U
  exact ((i1_freeSectionSpecialization_coordinates_continuous
    (ComplexPoint.openScheme Q U) k (s ≫ E.hom)).comp ho).congr
      (fun x => (i1_conormalFrameCoordinates_sectionValue j k U E s x.1 x.2).symm)

end HodgeLean.Foundations.BundleThom
