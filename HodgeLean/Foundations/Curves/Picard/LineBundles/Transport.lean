import HodgeLean.Foundations.Curves.Picard.LineBundles.Defs

/-! # Pointed pullback and isomorphism classes

The comparison follows the literal square of base-point sections and parameter maps.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
open Families

/-- Canonical pullback comparison for the structure module.
Source: Stacks Project, Tag 01CA; Mathlib `pullbackObjUnitToUnit`. -/
def pullbackUnit {X Y : Scheme} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (unit Y) ≅ unit X :=
  by
    letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
      inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
    letI : (TopologicalSpace.Opens.map f.base).Final := inferInstance
    exact @asIso (SheafOfModules X.ringCatSheaf) _ _ _
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) inferInstance

example (X : Scheme) : (Scheme.Modules.pullback (𝟙 X)).obj (unit X) ≅ unit X :=
  pullbackUnit (𝟙 X)

/-- The tensor unit comparison for the sheafified tensor construction.
Source: Stacks Project, Tag 01CA; Mathlib `sheafificationAdjunction`. -/
def tensorUnit {X : Scheme} (M : X.Modules) : tensor (unit X) M ≅ M :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (MonoidalCategory.leftUnitor (show PresheafOfModulesOfCommRing X.presheaf from M.val)) ≪≫
  @asIso (SheafOfModules X.ringCatSheaf) _ _ _
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app M)
    inferInstance

example (X : Scheme) : tensor (unit X) (unit X) ≅ unit X := tensorUnit _

/-- The actual tensor map induced by two module morphisms.
Source: Stacks Project, Tag 01CA. -/
def tensorMap {X : Scheme} {M N P Q : X.Modules} (f : M ⟶ N) (g : P ⟶ Q) :
    tensor M P ⟶ tensor N Q :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom f.val g.val)

example {X : Scheme} (M : X.Modules) : tensor (unit X) M ⟶ tensor (unit X) M :=
  tensorMap (𝟙 _) (𝟙 _)

/-- Tensoring actual sheaf isomorphisms.
Source: Stacks Project, Tag 01CA. -/
def tensorIso {X : Scheme} {M N P Q : X.Modules} (e : M ≅ N) (f : P ≅ Q) :
    tensor M P ≅ tensor N Q :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (MonoidalCategory.tensorIso (C := PresheafOfModulesOfCommRing X.presheaf)
      (show (M.val : PresheafOfModulesOfCommRing X.presheaf) ≅ N.val from
        ⟨e.hom.val, e.inv.val, congrArg SheafOfModules.Hom.val e.hom_inv_id,
          congrArg SheafOfModules.Hom.val e.inv_hom_id⟩)
      (show (P.val : PresheafOfModulesOfCommRing X.presheaf) ≅ Q.val from
        ⟨f.hom.val, f.inv.val, congrArg SheafOfModules.Hom.val f.hom_inv_id,
          congrArg SheafOfModules.Hom.val f.inv_hom_id⟩))

example {X : Scheme} (M : X.Modules) : tensor M M ≅ tensor M M :=
  tensorIso (Iso.refl _) (Iso.refl _)

/-- A tensor-inverse realization of the module O(D), retaining its evaluation map.
Source: Stacks Project, Tag 01CR; Hartshorne II.6. -/
structure Associated {X : Scheme} (I : X.IdealSheafData) where
  line : Line X
  contraction : tensor (idealModule I) line.module ≅ unit X

example {X : Scheme} {I : X.IdealSheafData} (L : Associated I) :
    unit X ⟶ tensor (idealModule I) L.line.module := L.contraction.inv

/-- The canonical section of O(D) induced by the actual ideal inclusion.
Source: Hartshorne II.6, effective divisors and their sections. -/
def associatedSection {X : Scheme} {I : X.IdealSheafData} (L : Associated I) :
    unit X ⟶ L.line.module :=
  L.contraction.inv ≫ tensorMap (kernel.ι _) (𝟙 _) ≫ (tensorUnit _).hom

example {X : Scheme} {I : X.IdealSheafData} (L : Associated I) :
    unit X ⟶ L.line.module := associatedSection L

/-- The trivial line with its specified base-point rigidification.
Source: Kleiman, The Picard scheme, §4. -/
def trivialRigid (C T : Over (Spec ↧ℂ)) (b : Over.mk (𝟙 (Spec ↧ℂ)) ⟶ C) :
    Rigidified C T b where
  line := trivialLine _
  rigid := pullbackUnit _

example (C T : Over (Spec ↧ℂ)) (b : Over.mk (𝟙 (Spec ↧ℂ)) ⟶ C) :
    (trivialRigid C T b).line.module = unit (Product C T) := rfl

/-- Pulling back a rigidification along the actual parameter square.
Source: Kleiman, The Picard scheme, §4; Mathlib `Modules.pullbackComp`. -/
def pulledRigid {C T T' : Over (Spec ↧ℂ)} {b} (f : T' ⟶ T)
    (L : Rigidified C T b) :
    (Scheme.Modules.pullback (pointSection C T' b)).obj
      ((Scheme.Modules.pullback (productMap C f)).obj L.line.module) ≅ unit T'.left :=
  (Scheme.Modules.pullbackComp (pointSection C T' b) (productMap C f)).app _ ≪≫
  (Scheme.Modules.pullbackCongr (show pointSection C T' b ≫ productMap C f =
      f.left ≫ pointSection C T b by
    apply pullback.hom_ext <;> simp [pointSection, productMap, Category.assoc])).app _ ≪≫
  ((Scheme.Modules.pullbackComp f.left (pointSection C T b)).app _).symm ≪≫
  (Scheme.Modules.pullback f.left).mapIso L.rigid ≪≫ pullbackUnit f.left

example {C T T' : Over (Spec ↧ℂ)} {b} (f : T' ⟶ T) (L : Rigidified C T b) :
    (pulledRigid f L).hom ≫ (pulledRigid f L).inv = 𝟙 _ := Iso.hom_inv_id _

/-- Isomorphism classes of divisor-presented rigidified degree-zero families.
Source: Kleiman, The Picard scheme, §4. -/
def familySetoid (C T : Over (Spec ↧ℂ)) (b : Over.mk (𝟙 (Spec ↧ℂ)) ⟶ C) :
    Setoid (DegreeZero C T b) where
  r L M := Nonempty (RigidIso L.bundle M.bundle)
  iseqv := {
    refl := fun L => ⟨⟨Iso.refl _, by simp⟩⟩
    symm := by
      rintro L M ⟨e⟩
      refine ⟨⟨e.iso.symm, ?_⟩⟩
      rw [← e.respects, ← Category.assoc, ← Functor.map_comp]
      simp
    trans := by
      rintro L M N ⟨e⟩ ⟨f⟩
      refine ⟨⟨e.iso ≪≫ f.iso, ?_⟩⟩
      simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
      rw [f.respects, e.respects] }

example {C T : Over (Spec ↧ℂ)} {b} (L : DegreeZero C T b) :
    (familySetoid C T b).r L L := ⟨⟨Iso.refl _, by simp⟩⟩

/-- The divisor-presented degree-zero family set; no identification with Picard is made.
Source: Kleiman, The Picard scheme, §4. -/
abbrev FamilyClasses (C T : Over (Spec ↧ℂ)) (b : Over.mk (𝟙 (Spec ↧ℂ)) ⟶ C) :=
  Quotient (familySetoid C T b)

example {C T : Over (Spec ↧ℂ)} {b} (L : DegreeZero C T b) : FamilyClasses C T b :=
  Quotient.mk _ L

end HodgeLean.Foundations.Curves.Picard.LineBundles
