import HodgeLean.Foundations.Program.G32Native.PairedC3LocalLiftSummands
import HodgeLean.Foundations.Program.G32Native.PairedC3RetainedSubobject

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Separate the original trivial block from all negative summands globally. -/
def pairedC3GlobalMixedIso (k a : ℕ) : (b : ℕ) →
    pairedC3SplitBundle k a b ≅
      SheafOfModules.free (Fin a) ⊞ pairedC3SplitBundle k 0 b
  | 0 => pairedC3RightEmptyIso _
  | b + 1 => biprod.mapIso (pairedC3GlobalMixedIso k a b) (Iso.refl _) ≪≫
      biprod.associator _ _ _

/-- The global block decomposition retains the original inclusion and scale. -/
theorem paired_c3_global_mixed_inclusion (k a b : ℕ) :
    pairedC3TrivialInclusion k a b ≫ (pairedC3GlobalMixedIso k a b).hom =
      biprod.inl := by
  induction b with
  | zero => exact Category.id_comp _
  | succ b ih =>
    simp only [pairedC3TrivialInclusion, pairedC3GlobalMixedIso,
      Iso.trans_hom, biprod.mapIso_hom, Category.assoc, biprod.inl_map_assoc]
    rw [← Category.assoc, ih]
    apply biprod.hom_ext <;>
      simp only [biprod.associator_hom, biprod.lift_eq, Preadditive.comp_add,
        Preadditive.add_comp, add_zero, zero_add, Category.comp_id,
        Category.assoc, biprod.lift_fst,
        biprod.lift_snd, biprod.lift_fst_assoc, biprod.lift_snd_assoc,
        biprod.inl_fst_assoc, biprod.inl_snd_assoc, biprod.inl_fst,
        biprod.inl_snd, Category.id_comp, zero_comp, comp_zero]
    exact biprod.inl_fst

/-- A global retained presentation identifies the categorical quotient. -/
def pairedC3GlobalLiftCokernelIso (k a b : ℕ) (M : (pairedC3Proj k).Modules)
    (w : (SheafOfModules.free (Fin a) ⊞
      SheafOfModules.unit (pairedC3Proj k).ringCatSheaf) ⟶ M)
    (e : M ≅ pairedC3SplitBundle k a b ⊞
      SheafOfModules.unit (pairedC3Proj k).ringCatSheaf)
    (he : w ≫ e.hom = biprod.map (pairedC3TrivialInclusion k a b) (𝟙 _)) :
    cokernel w ≅ pairedC3SplitBundle k 0 b := by
  let ee := e ≪≫ biprod.mapIso (pairedC3GlobalMixedIso k a b) (Iso.refl _) ≪≫
    pairedC3MiddleLastIso _ _ _
  apply pairedC3RetainedCokernelIso w ee
  change w ≫ (e.hom ≫ _ ≫ _) = _
  simp only [biprod.mapIso_hom, Iso.refl_hom]
  rw [← Category.assoc, he, paired_c3_biprod_map_comp_assoc,
    paired_c3_global_mixed_inclusion, Category.id_comp,
    paired_c3_middle_last_inclusion]

end HodgeLean.Foundations.Program.G32Native
