import HodgeLean.Foundations.BundleThom.FreePointProjectionHelpers
import HodgeLean.Foundations.BundleThom.UnitSpecializationHelpers

/-! # Specialization of actual finite free sheaf sections

Coordinate projections retain the supplied section and point pullback.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleThom

/-- Specialize a free-sheaf section using the actual complex point and free comparison.
Source: Hartshorne, Algebraic Geometry, II.5, fibres of finite free sheaves. -/
def i1_freeSectionSpecialization (Q : Over (Spec ↧ℂ)) (k : ℕ)
    (s : SheafOfModules.unit.{0} Q.left.ringCatSheaf ⟶
      SheafOfModules.free.{0} (R := Q.left.ringCatSheaf) (Fin k)) (x : ComplexPoint Q) :
    SheafOfModules.unit.{0} (Spec ↧ℂ).ringCatSheaf ⟶
      SheafOfModules.free.{0} (R := (Spec ↧ℂ).ringCatSheaf) (Fin k) := by
  letI : (TopologicalSpace.Opens.map x.left.base).Final := inferInstance
  letI : (SheafOfModules.pushforward x.left.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward x.left).IsRightAdjoint)
  let F := Scheme.Modules.pullback x.left
  let u : F.obj (SheafOfModules.unit.{0} Q.left.ringCatSheaf) ⟶
      SheafOfModules.unit.{0} (Spec ↧ℂ).ringCatSheaf :=
    SheafOfModules.pullbackObjUnitToUnit x.left.toRingCatSheafHom
  letI : IsIso u := inferInstanceAs (IsIso
    (SheafOfModules.pullbackObjUnitToUnit (F := TopologicalSpace.Opens.map x.left.base)
      x.left.toRingCatSheafHom))
  exact inv u ≫ F.map s ≫
    (SheafOfModules.pullbackObjFreeIso x.left.toRingCatSheafHom (Fin k)).hom

/-- Coordinate projection commutes with specialization of the supplied free-sheaf section.
Source: Hartshorne, Algebraic Geometry, II.5, pullback of free module sections. -/
theorem i1_freeSectionProjection_pullback {S T : Scheme.{0}} (a : S ⟶ T) (k : ℕ)
    (s : SheafOfModules.unit.{0} T.ringCatSheaf ⟶
      SheafOfModules.free.{0} (R := T.ringCatSheaf) (Fin k)) (i : Fin k) :
    letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
      (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
    ((Scheme.Modules.pullback a).map s ≫
        (SheafOfModules.pullbackObjFreeIso a.toRingCatSheafHom (Fin k)).hom) ≫
      i1_freeSheafProjection S k i =
      (Scheme.Modules.pullback a).map (s ≫ i1_freeSheafProjection T k i) ≫
        SheafOfModules.pullbackObjUnitToUnit a.toRingCatSheafHom := by
  letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
  let F := Scheme.Modules.pullback a
  let p := SheafOfModules.pullbackObjFreeIso a.toRingCatSheafHom (Fin k)
  let u := SheafOfModules.pullbackObjUnitToUnit a.toRingCatSheafHom
  have hp : F.map (i1_freeSheafProjection T k i) ≫ u =
      p.hom ≫ i1_freeSheafProjection S k i := i1_freeSheafProjection_pullback a k i
  calc
    (F.map s ≫ p.hom) ≫ i1_freeSheafProjection S k i =
        F.map s ≫ (p.hom ≫ i1_freeSheafProjection S k i) := Category.assoc _ _ _
    _ = F.map s ≫ (F.map (i1_freeSheafProjection T k i) ≫ u) :=
      congrArg (fun z => F.map s ≫ z) hp.symm
    _ = F.map (s ≫ i1_freeSheafProjection T k i) ≫ u :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ u) (F.map_comp s (i1_freeSheafProjection T k i)).symm)

/-- Each specialized free-section coordinate is evaluation of its actual regular coefficient.
Source: Hartshorne, Algebraic Geometry, II.5, free sheaf sections and their fibres. -/
theorem i1_freeSectionSpecialization_coordinate (Q : Over (Spec ↧ℂ)) (k : ℕ)
    (s : SheafOfModules.unit.{0} Q.left.ringCatSheaf ⟶
      SheafOfModules.free.{0} (R := Q.left.ringCatSheaf) (Fin k))
    (x : ComplexPoint Q) (i : Fin k) :
    i1_freePointCoordinates k
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        (i1_freeSectionSpecialization Q k s x) (1 : Γ(Spec ↧ℂ, ⊤))) i =
      Point.evaluate ⊤ ((s ≫ i1_freeSheafProjection Q.left k i).val.app (.op ⊤)
        (1 : Γ(Q.left, ⊤))) x := by
  letI : (TopologicalSpace.Opens.map x.left.base).Final := inferInstance
  letI : (SheafOfModules.pushforward x.left.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward x.left).IsRightAdjoint)
  let F := Scheme.Modules.pullback x.left
  let G := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  let u : F.obj (SheafOfModules.unit.{0} Q.left.ringCatSheaf) ⟶
      SheafOfModules.unit.{0} (Spec ↧ℂ).ringCatSheaf :=
    SheafOfModules.pullbackObjUnitToUnit x.left.toRingCatSheafHom
  letI : IsIso u := inferInstanceAs (IsIso
    (SheafOfModules.pullbackObjUnitToUnit (F := TopologicalSpace.Opens.map x.left.base)
      x.left.toRingCatSheafHom))
  let p := SheafOfModules.pullbackObjFreeIso x.left.toRingCatSheafHom (Fin k)
  have ht : i1_freeSectionSpecialization Q k s x ≫
      i1_freeSheafProjection (Spec ↧ℂ) k i =
      inv u ≫ F.map (s ≫ i1_freeSheafProjection Q.left k i) ≫ u :=
    (Category.assoc _ _ _).trans
      (congrArg (fun z => inv u ≫ z) (i1_freeSectionProjection_pullback x.left k s i))
  have hm := congrArg (fun z :
      G.obj (SheafOfModules.unit.{0} (Spec ↧ℂ).ringCatSheaf) ⟶
        G.obj (SheafOfModules.unit.{0} (Spec ↧ℂ).ringCatSheaf) =>
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (z.hom (1 : Γ(Spec ↧ℂ, ⊤))))
    (G.map_comp (i1_freeSectionSpecialization Q k s x)
      (i1_freeSheafProjection (Spec ↧ℂ) k i)).symm
  have hv := congrArg (fun z : SheafOfModules.unit.{0} (Spec ↧ℂ).ringCatSheaf ⟶
      SheafOfModules.unit.{0} (Spec ↧ℂ).ringCatSheaf =>
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((G.map z).hom (1 : Γ(Spec ↧ℂ, ⊤)))) ht
  exact (i1_freePointCoordinates_projection k _ i).trans
    (hm.trans (hv.trans
      (i1_unitPullback_endomorphism_coefficient Q (s ≫ i1_freeSheafProjection Q.left k i) x)))

/-- The finite coordinates of an actual specialized free-sheaf section vary continuously.
Source: Hartshorne, Algebraic Geometry, II.5, analytification of free sheaf sections. -/
theorem i1_freeSectionSpecialization_coordinates_continuous (Q : Over (Spec ↧ℂ)) (k : ℕ)
    (s : SheafOfModules.unit.{0} Q.left.ringCatSheaf ⟶
      SheafOfModules.free.{0} (R := Q.left.ringCatSheaf) (Fin k)) :
    Continuous (fun x : ComplexPoint Q => i1_freePointCoordinates k
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        (i1_freeSectionSpecialization Q k s x) (1 : Γ(Spec ↧ℂ, ⊤)))) := by
  apply continuous_pi
  intro i
  exact (i1_regularEvaluation_global_continuous Q
    ((s ≫ i1_freeSheafProjection Q.left k i).val.app (.op ⊤)
      (1 : Γ(Q.left, ⊤)))).congr
        (fun x => (i1_freeSectionSpecialization_coordinate Q k s x i).symm)

end HodgeLean.Foundations.BundleThom
