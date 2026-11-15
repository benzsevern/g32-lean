import HodgeLean.Foundations.Program.G32Native.OriginalIdealAffineSectionNaturality

/-! # Typed inclusions for the original ideal module -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Algebraic HodgeLean.Foundations.Program

/-- The kernel inclusion with its domain retained as the original ideal module. -/
def conormalIdealInclusion {Q W : Scheme.{0}} (j : Q ⟶ W) :
    Conormal.idealModule j ⟶ SheafOfModules.unit.{0} W.ringCatSheaf :=
  kernel.ι (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)

/-- The original inclusion detects equality of ideal sections. -/
theorem idealSection_eq_of_typed_inclusion {Q W : Scheme.{0}} (j : Q ⟶ W)
    (s t : SheafOfModules.unit.{0} W.ringCatSheaf ⟶ Conormal.idealModule j)
    (h : s ≫ conormalIdealInclusion j = t ≫ conormalIdealInclusion j) : s = t :=
  idealSection_ext j s t h

/-- Equality of ideal sections preserves the typed inclusion equation. -/
theorem idealSection_inclusion_congr {Q W : Scheme.{0}} (j : Q ⟶ W)
    {s t : SheafOfModules.unit.{0} W.ringCatSheaf ⟶ Conormal.idealModule j}
    (h : s = t) : s ≫ conormalIdealInclusion j = t ≫ conormalIdealInclusion j :=
  congrArg (fun z => z ≫ conormalIdealInclusion j) h

/-- An ideal section in new source coordinates. -/
def conormalSourceIdealSection {Q Q' W : Scheme.{0}} (j : Q ⟶ W) (e : Q' ≅ Q)
    (s : SheafOfModules.unit.{0} W.ringCatSheaf ⟶ Conormal.idealModule j) :
    SheafOfModules.unit.{0} W.ringCatSheaf ⟶ Conormal.idealModule (e.hom ≫ j) :=
  s ≫ (s2e_idealModule_source_iso j e).hom

/-- Source coordinate transport preserves the typed ideal inclusion. -/
theorem conormalSourceIdealSection_inclusion {Q Q' W : Scheme.{0}}
    (j : Q ⟶ W) (e : Q' ≅ Q)
    (s : SheafOfModules.unit.{0} W.ringCatSheaf ⟶ Conormal.idealModule j) :
    conormalSourceIdealSection j e s ≫ conormalIdealInclusion (e.hom ≫ j) =
      s ≫ conormalIdealInclusion j := by
  dsimp only [conormalSourceIdealSection, conormalIdealInclusion]
  rw [Category.assoc, original_ideal_source_iso_inclusion]

/-- Source coordinate transport preserves the original scalar. -/
theorem conormalSourceIdealSection_scalar {Q Q' W : Scheme.{0}}
    (j : Q ⟶ W) (e : Q' ≅ Q)
    (s : SheafOfModules.unit.{0} W.ringCatSheaf ⟶ Conormal.idealModule j)
    (c : Γ(W, ⊤)) (hs : s ≫ conormalIdealInclusion j = f5sheaf_scal (X := W) c) :
    conormalSourceIdealSection j e s ≫ conormalIdealInclusion (e.hom ≫ j) =
      f5sheaf_scal (X := W) c :=
  (conormalSourceIdealSection_inclusion j e s).trans hs

/-- The affine ideal section retains its scalar through the typed inclusion. -/
theorem affineIdealModuleSection_typed_inclusion
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (u : RingHom.ker φ.hom) :
    affineIdealModuleSection R S φ u ≫ conormalIdealInclusion (Spec.map φ) =
      f5sheaf_scal ((Scheme.ΓSpecIso R).inv u.val) :=
  affineIdealModuleSection_inclusion_scalar R S φ u

/-- The original scalar identifies the affine ideal section uniquely. -/
theorem affineIdealModuleSection_typed_unique
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (u : RingHom.ker φ.hom)
    (t : SheafOfModules.unit.{0} (Spec R).ringCatSheaf ⟶ Conormal.idealModule (Spec.map φ))
    (ht : t ≫ conormalIdealInclusion (Spec.map φ) =
      f5sheaf_scal ((Scheme.ΓSpecIso R).inv u.val)) :
    t = affineIdealModuleSection R S φ u :=
  idealSection_eq_of_typed_inclusion (Spec.map φ) t _
    (ht.trans (affineIdealModuleSection_typed_inclusion R S φ u).symm)

end HodgeLean.Foundations.TubularEuler
