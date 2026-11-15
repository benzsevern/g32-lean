import HodgeLean.Foundations.Program.SchoenTowerL1aInvariantDiagram

/-! # The presheaf of invariant section rings

The actual contravariant diagram of invariant sections over target opens,
with its structure map from base sections. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The ring-valued presheaf of invariant functions on inverse images of target opens.
Source: Stacks Project, tag 04A9, the algebra of invariant functions. -/
def s2v_l1a_fixedSectionDiagram
    {X Y : Scheme} {T : Type*} (f : X ⟶ Y) (a : T → (X ⟶ X))
    (ha : ∀ t, a t ≫ f = f) : Y.Opensᵒᵖ ⥤ CommRingCat where
  obj U := CommRingCat.of (s2v_l1a_fixedSectionSubring f a ha U.unop)
  map {U V} i := CommRingCat.ofHom
    (s2v_l1a_fixedSectionRestriction f a ha U.unop V.unop i.unop.le)
  map_id U := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    apply Subtype.ext
    change (X.presheaf.map (𝟙 _)).hom (s : Γ(X, f ⁻¹ᵁ U.unop)) = s
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp {U V W} i j := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    apply Subtype.ext
    change (X.presheaf.map _).hom (s : Γ(X, f ⁻¹ᵁ U.unop)) =
      ((X.presheaf.map _) ≫ (X.presheaf.map _)).hom (s : Γ(X, f ⁻¹ᵁ U.unop))
    rw [← CategoryTheory.Functor.map_comp]
    rfl

example {X Y : Scheme} {T : Type*} (f : X ⟶ Y) (a : T → (X ⟶ X))
    (ha : ∀ t, a t ≫ f = f) (U : Y.Opens) :
    (s2v_l1a_fixedSectionDiagram f a ha).obj (.op U) =
      CommRingCat.of (s2v_l1a_fixedSectionSubring f a ha U) := rfl

/-- The actual structure morphism from base sections to the invariant section presheaf.
Source: Stacks Project, tag 04A9, the structure map to invariant functions. -/
def s2v_l1a_fixedSectionStructureMap
    {X Y : Scheme} {T : Type*} (f : X ⟶ Y) (a : T → (X ⟶ X))
    (ha : ∀ t, a t ≫ f = f) : Y.presheaf ⟶ s2v_l1a_fixedSectionDiagram f a ha where
  app U := CommRingCat.ofHom (s2v_l1a_baseToFixedSections f a ha U.unop)
  naturality {U V} i := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    apply Subtype.ext
    change (f.app V.unop).hom ((Y.presheaf.map i).hom s) =
      (X.presheaf.map (homOfLE (f.preimage_mono i.unop.le)).op).hom ((f.app U.unop).hom s)
    exact congrArg (fun g : Γ(Y, U.unop) ⟶ Γ(X, f ⁻¹ᵁ V.unop) => g.hom s)
      (f.naturality i)

example {X Y : Scheme} {T : Type*} (f : X ⟶ Y) (a : T → (X ⟶ X))
    (ha : ∀ t, a t ≫ f = f) (U : Y.Opens) :
    (s2v_l1a_fixedSectionStructureMap f a ha).app (.op U) =
      CommRingCat.ofHom (s2v_l1a_baseToFixedSections f a ha U) := rfl

end HodgeLean.Foundations.Program
