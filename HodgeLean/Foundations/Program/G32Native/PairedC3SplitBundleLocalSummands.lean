import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNSplittingMaps
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Tensor.Monoidal
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Local mixed-bundle frames retaining the original trivial subobject -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The free module on no generators is the actual zero object. -/
theorem paired_c3_free_zero_isZero {X : Scheme.{0}} :
    IsZero (SheafOfModules.free (R := X.ringCatSheaf) (Fin 0)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (SheafOfModules.freeHomEquiv (SheafOfModules.free (R := X.ringCatSheaf) (Fin 0))).injective
  funext i
  exact Fin.elim0 i

/-- Include a specified object as the first summand beside the empty free module. -/
def pairedC3RightEmptyIso {X : Scheme.{0}} (A : X.Modules) :
    A ≅ A ⊞ SheafOfModules.free (Fin 0) where
  hom := biprod.inl
  inv := biprod.fst
  hom_inv_id := biprod.inl_fst
  inv_hom_id := by
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.inl_fst, Category.comp_id, Category.id_comp]
    · exact paired_c3_free_zero_isZero.eq_of_tgt _ _

/-- Appending one unit generator gives the free module in the original sum order. -/
def pairedC3FreeSuccIso {X : Scheme.{0}} (b : ℕ) :
    (SheafOfModules.free (R := X.ringCatSheaf) (Fin b) : X.Modules) ⊞
      SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.free (Fin (b + 1)) :=
  biprod.mapIso (Iso.refl _)
    (coproductUniqueIso (fun _ : Fin 1 => SheafOfModules.unit X.ringCatSheaf)).symm ≪≫
    biprod.isoCoprod _ _ ≪≫ SheafOfModules.freeSumIso (Fin b) (Fin 1) ≪≫
      (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).mapIso finSumFinEquiv.toIso

section MapBiprod
variable {C D : Type*} [Category C] [Category D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms]
  (A B : C) [HasBinaryBiproduct A B] [PreservesBinaryBiproduct A B F]

/-- The canonical biproduct comparison retains the original first inclusion. -/
@[reassoc]
theorem paired_c3_map_biprod_inl :
    F.map (biprod.inl : A ⟶ A ⊞ B) ≫ (F.mapBiprod A B).hom = biprod.inl := by
  apply (cancel_mono (F.mapBiprod A B).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Functor.mapBiprod_inv, biprod.inl_desc]
end MapBiprod

/-- Frame the negative summands without replacing the original trivial subobject. -/
def pairedC3LocalMixedIso (k a : ℕ) (U : (pairedC3Proj k).Opens)
    (eL : (Scheme.Modules.pullback U.ι).obj (pairedC3NegativeLine k) ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) : (b : ℕ) →
    ((Scheme.Modules.pullback U.ι).obj (pairedC3SplitBundle k a b) ≅
      (Scheme.Modules.pullback U.ι).obj (SheafOfModules.free (Fin a)) ⊞
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin b) : U.toScheme.Modules))
  | 0 => pairedC3RightEmptyIso _
  | b + 1 => by
    let F := Scheme.Modules.pullback U.ι
    letI : PreservesBinaryBiproducts F :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts F
    exact F.mapBiprod _ _ ≪≫ biprod.mapIso (pairedC3LocalMixedIso k a U eL b) eL ≪≫
      biprod.associator _ _ _ ≪≫ biprod.mapIso (Iso.refl _) (pairedC3FreeSuccIso b)

/-- The local frame carries the same trivial directions to the first summand. -/
theorem paired_c3_local_mixed_iso_trivial (k a : ℕ) (U : (pairedC3Proj k).Opens)
    (eL : (Scheme.Modules.pullback U.ι).obj (pairedC3NegativeLine k) ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) (b : ℕ) :
    (Scheme.Modules.pullback U.ι).map (pairedC3TrivialInclusion k a b) ≫
      (pairedC3LocalMixedIso k a U eL b).hom = biprod.inl := by
  let F := Scheme.Modules.pullback U.ι
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  induction b with
  | zero =>
    change (Scheme.Modules.pullback U.ι).map
      (𝟙 (SheafOfModules.free (Fin a))) ≫ biprod.inl = biprod.inl
    rw [(Scheme.Modules.pullback U.ι).map_id, Category.id_comp]
  | succ b ih =>
    simp only [pairedC3TrivialInclusion, pairedC3LocalMixedIso, Functor.map_comp,
      Iso.trans_hom, Category.assoc, biprod.mapIso_hom]
    rw [paired_c3_map_biprod_inl_assoc, biprod.inl_map_assoc, ← Category.assoc, ih]
    apply biprod.hom_ext <;>
      simp only [Iso.refl_hom, Category.assoc, biprod.map_fst, biprod.map_snd, biprod.associator_hom,
        biprod.lift_eq, Preadditive.comp_add, Preadditive.add_comp,
        biprod.inl_fst_assoc, biprod.inl_snd_assoc, biprod.inr_fst_assoc, biprod.inr_snd_assoc,
        biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd,
        Category.comp_id, Category.id_comp, comp_zero, zero_comp, add_zero, zero_add]

end HodgeLean.Foundations.Program.G32Native
