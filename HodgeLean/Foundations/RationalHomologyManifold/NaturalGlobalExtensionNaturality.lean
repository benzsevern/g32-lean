import HodgeLean.Foundations.RationalHomologyManifold.NaturalGlobalExtension

/-! Naturality of the actual global extension comparison.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual global-extension map retains the original component identification in every natural degree.
Source: Mathlib, Algebra.Homology.Embedding.HomEquiv; component normalization of actual extension by zero.
HC no distance; AV milestone no distance.
-/
theorem naturalGlobalExtensionMap_component (X : TopCat.{0})
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ) (n : ℕ) :
    (naturalGlobalExtensionMap X K).f (n : ℤ) ≫
      ((((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj K).extendXIso
        ComplexShape.embeddingUpNat rfl).hom =
      (subdivisionGlobalSectionsFunctor X).map (K.extendXIso ComplexShape.embeddingUpNat rfl).hom := by
  change (ComplexShape.embeddingUpNat.liftExtend (naturalGlobalExtensionRestriction X K) _).f
      (ComplexShape.embeddingUpNat.f n) ≫ _ = _
  rw [ComplexShape.embeddingUpNat.liftExtend_f _ _ rfl]
  simp only [HomologicalComplex.restrictionXIso, eqToIso_refl, Iso.refl_inv,
    Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

#print axioms naturalGlobalExtensionMap_component
/-- The canonical actual global-extension comparison commutes with every original cochain morphism.
Source: Mathlib, Algebra.Homology.Embedding.Extend; naturality of component extension identifications.
HC no distance; AV milestone no distance.
-/
theorem naturalGlobalExtensionMap_naturality (X : TopCat.{0})
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ} (f : K ⟶ L) :
    ((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat) ≫ naturalGlobalExtensionMap X L =
      naturalGlobalExtensionMap X K ≫ HomologicalComplex.extendMap
        (((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).map f)
          ComplexShape.embeddingUpNat := by
  let E := subdivisionGlobalSectionsFunctor X
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : ∃ n, ComplexShape.embeddingUpNat.f n = i
  · obtain ⟨n, rfl⟩ := hi
    apply (cancel_mono (((E.mapHomologicalComplex (.up ℕ)).obj L).extendXIso
      ComplexShape.embeddingUpNat rfl).hom).mp
    change (E.map ((HomologicalComplex.extendMap f ComplexShape.embeddingUpNat).f (n : ℤ)) ≫
        (naturalGlobalExtensionMap X L).f (n : ℤ)) ≫ _ =
      ((naturalGlobalExtensionMap X K).f (n : ℤ) ≫
        (HomologicalComplex.extendMap ((E.mapHomologicalComplex (.up ℕ)).map f)
          ComplexShape.embeddingUpNat).f (n : ℤ)) ≫ _
    have h₁ : (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat).f (n : ℤ) =
        (K.extendXIso ComplexShape.embeddingUpNat rfl).hom ≫ f.f n ≫
          (L.extendXIso ComplexShape.embeddingUpNat rfl).inv :=
      HomologicalComplex.extendMap_f f ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl
    have h₂ : (HomologicalComplex.extendMap ((E.mapHomologicalComplex (.up ℕ)).map f)
        ComplexShape.embeddingUpNat).f (n : ℤ) =
      (((E.mapHomologicalComplex (.up ℕ)).obj K).extendXIso ComplexShape.embeddingUpNat rfl).hom ≫
        E.map (f.f n) ≫
          (((E.mapHomologicalComplex (.up ℕ)).obj L).extendXIso ComplexShape.embeddingUpNat rfl).inv :=
      HomologicalComplex.extendMap_f ((E.mapHomologicalComplex (.up ℕ)).map f)
        ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl
    rw [Category.assoc, naturalGlobalExtensionMap_component, h₁, h₂]
    simp only [E.map_comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id]
    have hv : E.map (L.extendXIso ComplexShape.embeddingUpNat (i := n) rfl).inv ≫
        (subdivisionGlobalSectionsFunctor X).map (L.extendXIso ComplexShape.embeddingUpNat (i := n) rfl).hom = 𝟙 _ := by
      change E.map _ ≫ E.map _ = _
      rw [← E.map_comp, Iso.inv_hom_id, E.map_id]
    rw [hv, Category.comp_id]
    simp only [← Category.assoc]
    rw [naturalGlobalExtensionMap_component]
  · exact (E.map_isZero (K.isZero_extend_X ComplexShape.embeddingUpNat i
      (by simpa only [not_exists] using hi))).eq_of_src _ _

#print axioms naturalGlobalExtensionMap_naturality
end HodgeLean.Foundations.RationalHomologyManifold
