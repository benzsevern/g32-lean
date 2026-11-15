import HodgeLean.Foundations.Program.G32Native.PairedC3NegativeSummand
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Original trivial directions under a negative summand permutation -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Moving a negative summand does not rescale or permute the original
trivial directions. -/
theorem paired_c3_negative_summand_trivial (k a b : ℕ) (i : Fin (b + 1)) :
    pairedC3TrivialInclusion k a (b + 1) ≫ (pairedC3NegativeSummandIso k a b i).hom =
      pairedC3TrivialInclusion k a b ≫
        (biprod.inr : pairedC3SplitBundle k a b ⟶
          pairedC3NegativeLine k ⊞ pairedC3SplitBundle k a b) := by
  induction b with
  | zero =>
    apply biprod.hom_ext <;>
      simp only [pairedC3SplitBundle, pairedC3TrivialInclusion, pairedC3NegativeSummandIso, Category.id_comp,
        Category.assoc, biprod.braiding_hom, biprod.lift_fst, biprod.lift_snd,
        biprod.inl_snd, biprod.inl_fst, biprod.inr_fst, biprod.inr_snd, biprod.lift_eq, Preadditive.comp_add, Preadditive.add_comp,
        comp_zero, zero_comp, Category.comp_id, Category.id_comp, add_zero, zero_add]
  | succ b ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · apply biprod.hom_ext <;>
        simp only [pairedC3SplitBundle, pairedC3NegativeSummandIso, Fin.lastCases_last, pairedC3TrivialInclusion,
          Category.assoc, biprod.braiding_hom, biprod.lift_fst, biprod.lift_snd,
          biprod.inl_snd, biprod.inl_fst, biprod.inr_fst, biprod.inr_snd, biprod.lift_eq, Preadditive.comp_add, Preadditive.add_comp,
          biprod.inr_fst_assoc, biprod.inr_snd_assoc,
          comp_zero, zero_comp, add_zero, zero_add, Category.comp_id]
    · simp only [pairedC3NegativeSummandIso, Fin.lastCases_castSucc, Iso.trans_hom,
        biprod.mapIso_hom]
      change (pairedC3TrivialInclusion k a (b + 1) ≫ biprod.inl) ≫
        (biprod.map (pairedC3NegativeSummandIso k a b j).hom (𝟙 _) ≫
          (biprod.associator _ _ _).hom) = _
      rw [Category.assoc, biprod.inl_map_assoc, ← Category.assoc, ih j]
      apply biprod.hom_ext <;>
        simp only [pairedC3SplitBundle, pairedC3TrivialInclusion, Category.assoc, biprod.associator_hom,
          biprod.lift_fst, biprod.lift_snd, biprod.inl_fst_assoc, biprod.inl_snd_assoc,
          biprod.inr_fst, biprod.inr_snd, biprod.lift_eq, Preadditive.comp_add, Preadditive.add_comp,
          biprod.inr_fst_assoc, biprod.inr_snd_assoc, comp_zero, zero_comp, add_zero, zero_add, Category.comp_id, Category.id_comp]

end HodgeLean.Foundations.Program.G32Native
