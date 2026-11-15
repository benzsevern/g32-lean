import HodgeLean.Foundations.BundleResolution.ChernExtendedExactHelpers
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Actual binary comparisons between offset-extended chain complexes

The additive extension functors identify the extended middle sums with
the sums of the individually extended complexes.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace HodgeLean.Foundations.BundleResolution

variable {A B C D : ChainComplex (ModuleCat.{0} ℚ) ℕ} (p : ℤ)

def i1_extendedBinaryComparison
    (a : A.extend (ComplexShape.embeddingUpIntLE p) ⟶ B.extend (ComplexShape.embeddingUpIntLE 0))
    (c : C.extend (ComplexShape.embeddingUpIntLE p) ⟶ D.extend (ComplexShape.embeddingUpIntLE 0)) :
    (A ⊞ C).extend (ComplexShape.embeddingUpIntLE p) ⟶
      (B ⊞ D).extend (ComplexShape.embeddingUpIntLE 0) := by
  let Fp := (ComplexShape.embeddingUpIntLE p).extendFunctor (ModuleCat.{0} ℚ)
  let F0 := (ComplexShape.embeddingUpIntLE 0).extendFunctor (ModuleCat.{0} ℚ)
  letI : PreservesBinaryBiproduct A C Fp := preservesBinaryBiproduct_of_preservesBinaryProduct Fp
  letI : PreservesBinaryBiproduct B D F0 := preservesBinaryBiproduct_of_preservesBinaryProduct F0
  exact (Fp.mapBiprod A C).hom ≫ biprod.map a c ≫ (F0.mapBiprod B D).inv

@[reassoc]
theorem i1_extendedBinaryComparison_fst
    (a : A.extend (ComplexShape.embeddingUpIntLE p) ⟶ B.extend (ComplexShape.embeddingUpIntLE 0))
    (c : C.extend (ComplexShape.embeddingUpIntLE p) ⟶ D.extend (ComplexShape.embeddingUpIntLE 0)) :
    i1_extendedBinaryComparison p a c ≫
        HomologicalComplex.extendMap (biprod.fst : B ⊞ D ⟶ B) (ComplexShape.embeddingUpIntLE 0) =
      HomologicalComplex.extendMap (biprod.fst : A ⊞ C ⟶ A) (ComplexShape.embeddingUpIntLE p) ≫ a := by
  let Fp := (ComplexShape.embeddingUpIntLE p).extendFunctor (ModuleCat.{0} ℚ)
  let F0 := (ComplexShape.embeddingUpIntLE 0).extendFunctor (ModuleCat.{0} ℚ)
  letI : PreservesBinaryBiproduct A C Fp := preservesBinaryBiproduct_of_preservesBinaryProduct Fp
  letI : PreservesBinaryBiproduct B D F0 := preservesBinaryBiproduct_of_preservesBinaryProduct F0
  change ((Fp.mapBiprod A C).hom ≫ biprod.map a c ≫ (F0.mapBiprod B D).inv) ≫
    F0.map biprod.fst = Fp.map biprod.fst ≫ a
  have h : F0.map (biprod.fst : B ⊞ D ⟶ B) = (F0.mapBiprod B D).hom ≫ biprod.fst := by
    rw [Functor.mapBiprod_hom, biprod.lift_fst]
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  erw [biprod.map_fst]
  rw [Functor.mapBiprod_hom]
  erw [biprod.lift_fst_assoc]

@[reassoc]
theorem i1_extendedBinaryComparison_snd
    (a : A.extend (ComplexShape.embeddingUpIntLE p) ⟶ B.extend (ComplexShape.embeddingUpIntLE 0))
    (c : C.extend (ComplexShape.embeddingUpIntLE p) ⟶ D.extend (ComplexShape.embeddingUpIntLE 0)) :
    i1_extendedBinaryComparison p a c ≫
        HomologicalComplex.extendMap (biprod.snd : B ⊞ D ⟶ D) (ComplexShape.embeddingUpIntLE 0) =
      HomologicalComplex.extendMap (biprod.snd : A ⊞ C ⟶ C) (ComplexShape.embeddingUpIntLE p) ≫ c := by
  let Fp := (ComplexShape.embeddingUpIntLE p).extendFunctor (ModuleCat.{0} ℚ)
  let F0 := (ComplexShape.embeddingUpIntLE 0).extendFunctor (ModuleCat.{0} ℚ)
  letI : PreservesBinaryBiproduct A C Fp := preservesBinaryBiproduct_of_preservesBinaryProduct Fp
  letI : PreservesBinaryBiproduct B D F0 := preservesBinaryBiproduct_of_preservesBinaryProduct F0
  change ((Fp.mapBiprod A C).hom ≫ biprod.map a c ≫ (F0.mapBiprod B D).inv) ≫
    F0.map biprod.snd = Fp.map biprod.snd ≫ c
  have h : F0.map (biprod.snd : B ⊞ D ⟶ D) = (F0.mapBiprod B D).hom ≫ biprod.snd := by
    rw [Functor.mapBiprod_hom, biprod.lift_snd]
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  erw [biprod.map_snd]
  rw [Functor.mapBiprod_hom]
  erw [biprod.lift_snd_assoc]

theorem i1_extendedBinaryComparison_lift
    {I J : ChainComplex (ModuleCat.{0} ℚ) ℕ}
    (a : A.extend (ComplexShape.embeddingUpIntLE p) ⟶ B.extend (ComplexShape.embeddingUpIntLE 0))
    (c : C.extend (ComplexShape.embeddingUpIntLE p) ⟶ D.extend (ComplexShape.embeddingUpIntLE 0))
    (t : I.extend (ComplexShape.embeddingUpIntLE p) ⟶ J.extend (ComplexShape.embeddingUpIntLE 0))
    (f : I ⟶ A) (g : I ⟶ C) (j : J ⟶ B) (l : J ⟶ D)
    (ha : HomologicalComplex.extendMap f (ComplexShape.embeddingUpIntLE p) ≫ a =
      t ≫ HomologicalComplex.extendMap j (ComplexShape.embeddingUpIntLE 0))
    (hc : HomologicalComplex.extendMap g (ComplexShape.embeddingUpIntLE p) ≫ c =
      t ≫ HomologicalComplex.extendMap l (ComplexShape.embeddingUpIntLE 0)) :
    HomologicalComplex.extendMap (biprod.lift f (-g)) (ComplexShape.embeddingUpIntLE p) ≫
        i1_extendedBinaryComparison p a c =
      t ≫ HomologicalComplex.extendMap (biprod.lift j (-l)) (ComplexShape.embeddingUpIntLE 0) := by
  let Fp := (ComplexShape.embeddingUpIntLE p).extendFunctor (ModuleCat.{0} ℚ)
  let F0 := (ComplexShape.embeddingUpIntLE 0).extendFunctor (ModuleCat.{0} ℚ)
  letI : PreservesBinaryBiproduct B D F0 := preservesBinaryBiproduct_of_preservesBinaryProduct F0
  apply (cancel_mono (F0.mapBiprod B D).hom).mp
  apply biprod.hom_ext
  · simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_fst]
    erw [i1_extendedBinaryComparison_fst]
    change Fp.map (biprod.lift f (-g)) ≫ Fp.map biprod.fst ≫ a =
      t ≫ F0.map (biprod.lift j (-l)) ≫ F0.map biprod.fst
    rw [← Category.assoc, ← Fp.map_comp, ← F0.map_comp]
    simp only [biprod.lift_fst]
    exact ha
  · simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_snd]
    erw [i1_extendedBinaryComparison_snd]
    change Fp.map (biprod.lift f (-g)) ≫ Fp.map biprod.snd ≫ c =
      t ≫ F0.map (biprod.lift j (-l)) ≫ F0.map biprod.snd
    rw [← Category.assoc, ← Fp.map_comp, ← F0.map_comp]
    simp only [biprod.lift_snd, Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg]
    exact congrArg Neg.neg hc

theorem i1_extendedBinaryComparison_desc
    {I J : ChainComplex (ModuleCat.{0} ℚ) ℕ}
    (a : A.extend (ComplexShape.embeddingUpIntLE p) ⟶ B.extend (ComplexShape.embeddingUpIntLE 0))
    (c : C.extend (ComplexShape.embeddingUpIntLE p) ⟶ D.extend (ComplexShape.embeddingUpIntLE 0))
    (t : I.extend (ComplexShape.embeddingUpIntLE p) ⟶ J.extend (ComplexShape.embeddingUpIntLE 0))
    (f : A ⟶ I) (g : C ⟶ I) (j : B ⟶ J) (l : D ⟶ J)
    (ha : a ≫ HomologicalComplex.extendMap j (ComplexShape.embeddingUpIntLE 0) =
      HomologicalComplex.extendMap f (ComplexShape.embeddingUpIntLE p) ≫ t)
    (hc : c ≫ HomologicalComplex.extendMap l (ComplexShape.embeddingUpIntLE 0) =
      HomologicalComplex.extendMap g (ComplexShape.embeddingUpIntLE p) ≫ t) :
    i1_extendedBinaryComparison p a c ≫
        HomologicalComplex.extendMap (biprod.desc j l) (ComplexShape.embeddingUpIntLE 0) =
      HomologicalComplex.extendMap (biprod.desc f g) (ComplexShape.embeddingUpIntLE p) ≫ t := by
  let Fp := (ComplexShape.embeddingUpIntLE p).extendFunctor (ModuleCat.{0} ℚ)
  let F0 := (ComplexShape.embeddingUpIntLE 0).extendFunctor (ModuleCat.{0} ℚ)
  letI : PreservesBinaryBiproduct A C Fp := preservesBinaryBiproduct_of_preservesBinaryProduct Fp
  letI : PreservesBinaryBiproduct B D F0 := preservesBinaryBiproduct_of_preservesBinaryProduct F0
  have h0 : (F0.mapBiprod B D).inv ≫ F0.map (biprod.desc j l) =
      biprod.desc (F0.map j) (F0.map l) := by
    apply biprod.mapBiprod_inv_map_desc
  have hp : (Fp.mapBiprod A C).inv ≫ Fp.map (biprod.desc f g) =
      biprod.desc (Fp.map f) (Fp.map g) := by
    apply biprod.mapBiprod_inv_map_desc
  apply (cancel_epi (Fp.mapBiprod A C).inv).mp
  change (Fp.mapBiprod A C).inv ≫
      (((Fp.mapBiprod A C).hom ≫ biprod.map a c ≫ (F0.mapBiprod B D).inv) ≫
        F0.map (biprod.desc j l)) =
    (Fp.mapBiprod A C).inv ≫ (Fp.map (biprod.desc f g) ≫ t)
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [h0, ← Category.assoc (Fp.mapBiprod A C).inv (Fp.map (biprod.desc f g)) t, hp]
  apply biprod.hom_ext'
  · erw [biprod.inl_map_assoc, biprod.inl_desc_assoc, biprod.inl_desc]
    exact ha
  · erw [biprod.inr_map_assoc, biprod.inr_desc_assoc, biprod.inr_desc]
    exact hc

end HodgeLean.Foundations.BundleResolution
