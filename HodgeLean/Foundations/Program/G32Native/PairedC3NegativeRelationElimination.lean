import HodgeLean.Foundations.Program.G32Native.PairedC3NegativeSummandMaps
import HodgeLean.Foundations.Program.G32Native.PairedC3RetainedSubobject

/-! # Elimination retaining the original trivial directions and lifted generator -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

section Associator
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C] (A B D : C)

/-- The associator retains the middle summand. -/
@[reassoc]
theorem paired_c3_associator_middle :
    (biprod.inr : B ⟶ A ⊞ B) ≫ biprod.inl ≫ (biprod.associator A B D).hom =
      biprod.inl ≫ biprod.inr := by cat_disch

/-- The associator retains the last summand. -/
@[reassoc]
theorem paired_c3_associator_last :
    (biprod.inr : D ⟶ (A ⊞ B) ⊞ D) ≫ (biprod.associator A B D).hom =
      biprod.inr ≫ biprod.inr := by cat_disch
end Associator

/-- An invertible negative coefficient removes exactly that summand,
retaining the actual trivial directions and actual lifted unit generator. -/
theorem paired_c3_negative_relation_elimination
    (k a b : ℕ) (M : (pairedC3Proj k).Modules)
    (r : pairedC3NegativeLine k ⟶ pairedC3SplitBundle k a (b + 1) ⊞
      SheafOfModules.unit (pairedC3Proj k).ringCatSheaf)
    (v : pairedC3SplitBundle k a (b + 1) ⊞
      SheafOfModules.unit (pairedC3Proj k).ringCatSheaf ⟶ M)
    (hrv : r ≫ v = 0) (hP : (ShortComplex.mk r v hrv).ShortExact)
    (i : Fin (b + 1)) [IsIso (r ≫ biprod.fst ≫ pairedC3NegativeProjection k a b i)] :
    ∃ e : M ≅ pairedC3SplitBundle k a b ⊞ SheafOfModules.unit (pairedC3Proj k).ringCatSheaf,
      biprod.map (pairedC3TrivialInclusion k a (b + 1)) (𝟙 _) ≫ v ≫ e.hom =
        biprod.map (pairedC3TrivialInclusion k a b) (𝟙 _) := by
  let es := biprod.mapIso (pairedC3NegativeSummandIso k a b i) (Iso.refl
      (SheafOfModules.unit (pairedC3Proj k).ringCatSheaf)) ≪≫ biprod.associator _ _ _
  let rr := r ≫ es.hom
  let vv := es.inv ≫ v
  have hrr : rr ≫ vv = 0 := by
    simp only [rr, vv, Category.assoc, Iso.hom_inv_id_assoc, hrv]
  let eP : ShortComplex.mk r v hrv ≅ ShortComplex.mk rr vv hrr :=
    ShortComplex.isoMk (Iso.refl _) es (Iso.refl _)
      (by change 𝟙 _ ≫ rr = r ≫ es.hom; rw [Category.id_comp])
      (by change es.hom ≫ (es.inv ≫ v) = v ≫ 𝟙 _
          rw [Iso.hom_inv_id_assoc, Category.comp_id])
  have hnew := ShortComplex.shortExact_of_iso eP hP
  have hcoeff : rr ≫ biprod.fst = r ≫ biprod.fst ≫ pairedC3NegativeProjection k a b i := by
    simp only [rr, es, pairedC3NegativeProjection, Iso.trans_hom, biprod.mapIso_hom,
      Category.assoc, biprod.associator_hom, biprod.lift_fst, biprod.map_fst_assoc]
  letI : IsIso (rr ≫ biprod.fst) := by rw [hcoeff]; infer_instance
  obtain ⟨e, he, _, _⟩ := paired_c3_retained_presentation_iso rr vv hrr hnew.gIsCokernel
  have hw : biprod.map (pairedC3TrivialInclusion k a (b + 1)) (𝟙 _) ≫ es.hom =
      biprod.map (pairedC3TrivialInclusion k a b) (𝟙 _) ≫ biprod.inr := by
    apply biprod.hom_ext'
    · simp only [es, Iso.trans_hom, biprod.mapIso_hom, Iso.refl_hom, Category.assoc,
        biprod.inl_map_assoc]
      rw [← Category.assoc, paired_c3_negative_summand_trivial]
      simp only [Category.assoc, paired_c3_associator_middle]
    · simp only [es, Iso.trans_hom, biprod.mapIso_hom, Iso.refl_hom, Category.assoc,
        biprod.inr_map_assoc, Category.id_comp, paired_c3_associator_last]
  refine ⟨e, ?_⟩
  calc
    _ = biprod.map (pairedC3TrivialInclusion k a (b + 1)) (𝟙 _) ≫ es.hom ≫ vv ≫ e.hom := by
      simp only [vv, Category.assoc, Iso.hom_inv_id_assoc]
    _ = biprod.map (pairedC3TrivialInclusion k a b) (𝟙 _) ≫ biprod.inr ≫ vv ≫ e.hom := by
      rw [← Category.assoc, ← Category.assoc, hw, Category.assoc, Category.assoc]
    _ = _ := by
      simp only [he, pairedC3RelationProjection, biprod.inr_desc, Category.comp_id]

end HodgeLean.Foundations.Program.G32Native
