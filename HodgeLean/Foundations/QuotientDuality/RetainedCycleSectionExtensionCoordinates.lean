import HodgeLean.Foundations.QuotientDuality.ProperCycleChainExtensionSections
import HodgeConjecture.Mathlib.Algebra.Homology.MapExtend

/-! # Canonical coordinates of the original section-extension comparison -/

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The original section-extension comparison has the canonical inverse mapping coordinates. -/
lemma retained_section_extension_canonical
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) [F.Additive]
    (K : ChainComplex C ℕ) :
    (properCycle_section_functor_extend_iso F K).hom =
      (mapExtendCanonicalIso F K ComplexShape.embeddingDownNat).inv := by
  let E (a : Option ℕ) :
      extend.X ((F.mapHomologicalComplex (.down ℕ)).obj K) a ≅ F.obj (extend.X K a) :=
    match a with
    | some _ => Iso.refl _
    | none => (isZero_zero D).iso (F.map_isZero (isZero_zero C))
  have h (a : Option ℕ) : (E a).hom = (mapExtendCanonicalXIso F K a).inv := by
    cases a with
    | none => exact (isZero_zero D).eq_of_src _ _
    | some n => rfl
  ext i : 1
  exact h (ComplexShape.embeddingDownNat.r i)

/-- Natural transformations of section functors respect the original regrading coordinates. -/
lemma retained_section_extension_naturality
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasZeroObject D] (F G : C ⥤ D) [F.Additive] [G.Additive]
    (τ : F ⟶ G) (K : ChainComplex C ℕ) :
    (properCycle_section_functor_extend_iso F K).hom ≫
      (τ.mapHomologicalComplex (.up ℤ)).app (K.extend ComplexShape.embeddingDownNat) =
    extendMap ((τ.mapHomologicalComplex (.down ℕ)).app K) ComplexShape.embeddingDownNat ≫
      (properCycle_section_functor_extend_iso G K).hom := by
  simp only [retained_section_extension_canonical]
  apply (cancel_mono (mapExtendCanonicalIso G K ComplexShape.embeddingDownNat).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [mapExtendCanonicalIso_natTrans F K ComplexShape.embeddingDownNat τ,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end HodgeLean.Foundations.QuotientDuality
