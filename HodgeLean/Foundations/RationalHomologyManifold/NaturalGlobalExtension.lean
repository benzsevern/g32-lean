import HodgeLean.Foundations.RationalHomologyManifold.BoundedSoftQuasiIso
import HodgeLean.Foundations.RationalHomologyManifold.ZeroSheafSoftness
import Mathlib.Algebra.Homology.Embedding.HomEquiv
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! Actual global sections and extension of natural-degree complexes.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The canonical natural-degree restriction of global sections of an extended complex retains its original components.
Source: Mathlib, Algebra.Homology.Embedding.Extend; actual global sections under extension by zero.
HC no distance; AV milestone no distance.
-/
def naturalGlobalExtensionRestriction (X : TopCat.{0})
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ) :
    ((((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (.up ℤ)).obj
      (K.extend ComplexShape.embeddingUpNat)).restriction ComplexShape.embeddingUpNat) ⟶
      ((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj K where
  f n := (subdivisionGlobalSectionsFunctor X).map
    (K.extendXIso ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)).hom
  comm' i j hij := by
    let E := subdivisionGlobalSectionsFunctor X
    change E.map (K.extendXIso ComplexShape.embeddingUpNat rfl).hom ≫ E.map (K.d i j) =
      E.map ((K.extend ComplexShape.embeddingUpNat).d _ _) ≫
        E.map (K.extendXIso ComplexShape.embeddingUpNat rfl).hom
    rw [← E.map_comp, ← E.map_comp]
    congr 1
    rw [K.extend_d_eq ComplexShape.embeddingUpNat rfl rfl]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

#print axioms naturalGlobalExtensionRestriction
/-- Global sections of the actual extension map canonically to the extension of global sections.
Source: Mathlib, Algebra.Homology.Embedding.HomEquiv; extension by zero and the original global-section functor.
HC no distance; AV milestone no distance.
-/
def naturalGlobalExtensionMap (X : TopCat.{0})
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ) :
    (((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (.up ℤ)).obj
      (K.extend ComplexShape.embeddingUpNat)) ⟶
    ((((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj K).extend
      ComplexShape.embeddingUpNat) :=
  ComplexShape.embeddingUpNat.liftExtend (naturalGlobalExtensionRestriction X K) (by
    intro j hj i' hi'
    exact ((subdivisionGlobalSectionsFunctor X).map_isZero
      (K.isZero_extend_X ComplexShape.embeddingUpNat i' (hj.notMem hi'))).eq_of_src _ _)

#print axioms naturalGlobalExtensionMap
/-- The canonical natural-degree global-extension comparison is invertible in every integer degree.
Source: Mathlib, Algebra.Homology.Embedding.Extend; the zero terms outside the embedding range.
HC no distance; AV milestone no distance.
-/
theorem naturalGlobalExtensionMap_isIso (X : TopCat.{0})
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ) :
    IsIso (naturalGlobalExtensionMap X K) := by
  let E := subdivisionGlobalSectionsFunctor X
  letI : ∀ i, IsIso ((naturalGlobalExtensionMap X K).f i) := by
    intro i
    by_cases hi : ∃ n, ComplexShape.embeddingUpNat.f n = i
    · obtain ⟨n, hn⟩ := hi
      change IsIso ((ComplexShape.embeddingUpNat.liftExtend
        (naturalGlobalExtensionRestriction X K) _).f i)
      rw [ComplexShape.embeddingUpNat.isIso_liftExtend_f_iff _ _ hn]
      change IsIso (E.map (K.extendXIso ComplexShape.embeddingUpNat rfl).hom)
      infer_instance
    · have hK := E.map_isZero (K.isZero_extend_X ComplexShape.embeddingUpNat i (by simpa only [not_exists] using hi))
      have hL := HomologicalComplex.isZero_extend_X
        ((E.mapHomologicalComplex (.up ℕ)).obj K) ComplexShape.embeddingUpNat i (by simpa only [not_exists] using hi)
      exact hK.isIso hL _
  exact HomologicalComplex.Hom.isIso_of_components _

#print axioms naturalGlobalExtensionMap_isIso
end HodgeLean.Foundations.RationalHomologyManifold
