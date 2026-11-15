import HodgeLean.Foundations.Program.G32Native.PairedC3SplitBundleLocalSummands
import HodgeLean.Foundations.Program.G32Native.PairedC3DualInvertible

/-! # Local summands for the actual lifted map after relation elimination -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

section Permutation
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

/-- Interchange the last two summands while retaining the first. -/
def pairedC3MiddleLastIso (A B D : C) : (A ⊞ B) ⊞ D ≅ (A ⊞ D) ⊞ B :=
  biprod.associator A B D ≪≫ biprod.mapIso (Iso.refl A) (biprod.braiding B D) ≪≫
    (biprod.associator A D B).symm

/-- The permutation carries the retained first and last directions to the first block. -/
@[reassoc]
theorem paired_c3_middle_last_inclusion (A B D : C) :
    biprod.map (biprod.inl : A ⟶ A ⊞ B) (𝟙 D) ≫ (pairedC3MiddleLastIso A B D).hom =
      biprod.inl := by
  dsimp only [pairedC3MiddleLastIso]
  cat_disch

/-- Composition of block maps retains both original components. -/
@[reassoc]
theorem paired_c3_biprod_map_comp {A B D E G H : C}
    (f : A ⟶ B) (g : D ⟶ E) (h : B ⟶ G) (i : E ⟶ H) :
    biprod.map f g ≫ biprod.map h i = biprod.map (f ≫ h) (g ≫ i) := by cat_disch
end Permutation

section Naturality
variable {C D : Type*} [Category C] [Category D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesBinaryBiproducts F]

/-- The canonical comparison of biproducts retains both mapped arrows. -/
@[reassoc]
theorem paired_c3_map_biprod_natural {A B A' B' : C} (f : A ⟶ A') (g : B ⟶ B') :
    F.map (biprod.map f g) ≫ (F.mapBiprod A' B').hom =
      (F.mapBiprod A B).hom ≫ biprod.map (F.map f) (F.map g) := by
  apply biprod.hom_ext <;>
    simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_fst, biprod.lift_snd, biprod.lift_fst_assoc, biprod.lift_snd_assoc,
      biprod.map_fst, biprod.map_snd, biprod.map_fst_assoc, biprod.map_snd_assoc,
      ← F.map_comp]
end Naturality

section RetainedFunctor
variable {C D : Type*} [Category C] [Category D]
  [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesBinaryBiproducts F]

/-- Transport a specified subobject through two compatible summand identifications. -/
theorem paired_c3_functor_retained_summands {A B O M : C}
    (i : A ⟶ B) (w : A ⊞ O ⟶ M) (e : M ≅ B ⊞ O)
    (he : w ≫ e.hom = biprod.map i (𝟙 O))
    (T : D) (em : F.obj B ≅ F.obj A ⊞ T)
    (hem : F.map i ≫ em.hom = biprod.inl) :
    ∃ ee : F.obj M ≅ F.obj (A ⊞ O) ⊞ T, F.map w ≫ ee.hom = biprod.inl := by
  let I0 := F.mapBiprod A O
  let I1 := F.mapBiprod B O
  let ep := pairedC3MiddleLastIso (F.obj A) T (F.obj O)
  let ee := F.mapIso e ≪≫ I1 ≪≫ biprod.mapIso em (Iso.refl (F.obj O)) ≪≫ ep ≪≫
    biprod.mapIso I0.symm (Iso.refl T)
  refine ⟨ee, ?_⟩
  change F.map w ≫ (F.map e.hom ≫ I1.hom ≫ biprod.map em.hom (𝟙 _) ≫
    ep.hom ≫ biprod.map I0.inv (𝟙 _)) = biprod.inl
  rw [← Category.assoc (F.map w) (F.map e.hom), ← F.map_comp, he,
    paired_c3_map_biprod_natural_assoc, F.map_id, paired_c3_biprod_map_comp_assoc,
    hem, Category.id_comp]
  rw [paired_c3_middle_last_inclusion_assoc, biprod.inl_map, Iso.hom_inv_id_assoc]
end RetainedFunctor

/-- A generator-preserving global elimination gives the precise local
summands required by the supplied lifted-map sequence. -/
theorem paired_c3_local_lift_summands
    (k a b : ℕ) (M : (pairedC3Proj k).Modules)
    (w : (SheafOfModules.free (R := (pairedC3Proj k).ringCatSheaf) (Fin a) ⊞
      SheafOfModules.unit (pairedC3Proj k).ringCatSheaf) ⟶ M)
    (e : M ≅ pairedC3SplitBundle k a b ⊞ SheafOfModules.unit (pairedC3Proj k).ringCatSheaf)
    (he : w ≫ e.hom = biprod.map (pairedC3TrivialInclusion k a b)
      (𝟙 (SheafOfModules.unit (pairedC3Proj k).ringCatSheaf))) :
    ∀ x : pairedC3Proj k, ∃ U : (pairedC3Proj k).Opens, x ∈ U ∧
      ∃ ee : (Scheme.Modules.pullback U.ι).obj M ≅
          (Scheme.Modules.pullback U.ι).obj (SheafOfModules.free (R := (pairedC3Proj k).ringCatSheaf) (Fin a) ⊞
            SheafOfModules.unit (pairedC3Proj k).ringCatSheaf) ⊞
            (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin b) : U.toScheme.Modules),
        (Scheme.Modules.pullback U.ι).map w ≫ ee.hom = biprod.inl := by
  intro x
  obtain ⟨U, hx, ⟨eL⟩⟩ := (paired_c3_dual_invertible
    (ProjSpace.isInvertible_twistingSheaf ℂ k)).exists_trivialization x
  let F := Scheme.Modules.pullback U.ι
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  obtain ⟨ee, hee⟩ := paired_c3_functor_retained_summands F
    (pairedC3TrivialInclusion k a b) w e he
    (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin b))
    (pairedC3LocalMixedIso k a U eL b) (paired_c3_local_mixed_iso_trivial k a U eL b)
  exact ⟨U, hx, ee, hee⟩

end HodgeLean.Foundations.Program.G32Native
