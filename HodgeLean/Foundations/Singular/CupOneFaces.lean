import HodgeLean.Foundations.Singular.Cup

/-!
# Faces for Steenrod cup-one

The outer and interval inclusions, and their six deletion identities, form the
combinatorial input to the cup-one differential identity in `CupOne.lean`.
HC no distance; AV milestone no distance. S6 retires nothing alone.
-/

noncomputable section
open CategoryTheory Limits AlgebraicTopology.Simplicial
open scoped Simplicial
open Finset
namespace HodgeLean.Foundations.Singular
attribute [local implicit_reducible] ShortComplex.moduleCatMk ShortComplex.moduleCatLeftHomologyData
variable {R : Type} [CommRing R] (Y : TopCat.{0})

/-- The outer face of the `j`th cup-one summand for input degrees `p + 1`, `q + 1`.
Source: Steenrod, *Products of cocycles and extensions of mappings*, Ann. Math. 48
(1947), 290–320, cup-one construction; explicit convention in Porter–Suciu, equation (4.5).
-/
def cupOneOuterInclusion (p q : ℕ) (j : Fin (p + 1)) :
    SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk (p + q + 1) :=
  SimplexCategory.mkHom
    { toFun := fun k => ⟨if k.val ≤ j.val then k.val else k.val + q, by
        split <;> omega⟩
      monotone' := by
        intro a b hab
        change (if a.val ≤ j.val then a.val else a.val + q) ≤
          (if b.val ≤ j.val then b.val else b.val + q)
        have hab' : a.val ≤ b.val := hab
        split <;> split <;> omega }

/-- The interval face of the `j`th cup-one summand for input degrees `p + 1`, `q + 1`.
Source: Steenrod, *Products of cocycles and extensions of mappings*, Ann. Math. 48
(1947), 290–320, cup-one construction; explicit convention in Porter–Suciu, equation (4.5).
-/
def cupOneInnerInclusion (p q : ℕ) (j : Fin (p + 1)) :
    SimplexCategory.mk (q + 1) ⟶ SimplexCategory.mk (p + q + 1) :=
  SimplexCategory.mkHom
    { toFun := fun k => ⟨j.val + k.val, by omega⟩
      monotone' := by intro a b hab; change j.val + a.val ≤ j.val + b.val; omega }

example : cupOneOuterInclusion 0 0 0 = 𝟙 _ := by ext i; fin_cases i <;> rfl
example : cupOneInnerInclusion 0 0 0 = 𝟙 _ := by ext i; fin_cases i <;> rfl

/-- Deleting a vertex before the inner interval shifts its starting index by one.
Source: constructed here from Steenrod (1947), cup-one face formula.
-/
theorem cupOneInnerInclusion_comp_earlyFace (p q : ℕ) (j : Fin (p + 1)) (i : Fin (p + q + 3))
    (hi : i.val ≤ j.val) :
    cupOneInnerInclusion p q j ≫ SimplexCategory.δ i =
      cupOneInnerInclusion (p + 1) q j.succ ≫
        eqToHom (congrArg SimplexCategory.mk (by omega : p + 1 + q + 1 = p + q + 1 + 1)) := by
  ext k
  simp only [cupOneInnerInclusion, SimplexCategory.δ,
    SimplexCategory.len_mk, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
    Fin.succAboveOrderEmb_apply, SimplexCategory.eqToHom_toOrderHom]
  rw [Fin.succAbove_of_le_castSucc]
  · change j.val + k.val + 1 = j.val + 1 + k.val
    omega
  · change i.val ≤ j.val + k.val
    omega

/-- Deleting a vertex after the inner interval preserves its starting index.
Source: constructed here from Steenrod (1947), cup-one face formula.
-/
theorem cupOneInnerInclusion_comp_lateFace (p q : ℕ) (j : Fin (p + 1)) (i : Fin (p + q + 3))
    (hi : j.val + q + 1 < i.val) :
    cupOneInnerInclusion p q j ≫ SimplexCategory.δ i =
      cupOneInnerInclusion (p + 1) q j.castSucc ≫
        eqToHom (congrArg SimplexCategory.mk (by omega : p + 1 + q + 1 = p + q + 1 + 1)) := by
  ext k
  simp only [cupOneInnerInclusion, SimplexCategory.δ,
    SimplexCategory.len_mk, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
    Fin.succAboveOrderEmb_apply, SimplexCategory.eqToHom_toOrderHom]
  rw [Fin.succAbove_of_castSucc_lt]
  · rfl
  · change j.val + k.val < i.val
    have hk : k.val < q + 2 := k.isLt
    omega

/-- Deleting an interior vertex is the corresponding face of the enlarged inner interval.
Source: constructed here from Steenrod (1947), cup-one face formula.
-/
theorem cupOneInnerInclusion_comp_middleFace (p q : ℕ) (j : Fin (p + 1)) (i : Fin (p + q + 3))
    (h₁ : j.val < i.val) (h₂ : i.val ≤ j.val + q + 1) :
    cupOneInnerInclusion p q j ≫ SimplexCategory.δ i =
      SimplexCategory.δ (⟨i.val - j.val, by omega⟩ : Fin (q + 3)) ≫
        cupOneInnerInclusion p (q + 1) j ≫
        eqToHom (congrArg SimplexCategory.mk (by omega : p + (q + 1) + 1 = p + q + 1 + 1)) := by
  ext k
  simp only [cupOneInnerInclusion, SimplexCategory.δ,
    SimplexCategory.len_mk, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
    Fin.succAboveOrderEmb_apply, SimplexCategory.eqToHom_toOrderHom]
  by_cases hk : k.val < i.val - j.val
  · rw [Fin.succAbove_of_castSucc_lt, Fin.succAbove_of_castSucc_lt]
    · rfl
    · exact hk
    · change j.val + k.val < i.val
      omega
  · rw [Fin.succAbove_of_le_castSucc, Fin.succAbove_of_le_castSucc]
    · change j.val + k.val + 1 = j.val + (k.val + 1)
      omega
    · change i.val - j.val ≤ k.val
      omega
    · change i.val ≤ j.val + k.val
      omega

/-- Deleting an interior vertex enlarges the omitted interval in the outer face.
Source: constructed here from Steenrod (1947), cup-one face formula.
-/
theorem cupOneOuterInclusion_comp_middleFace (p q : ℕ) (j : Fin (p + 1)) (i : Fin (p + q + 3))
    (h₁ : j.val < i.val) (h₂ : i.val ≤ j.val + q + 1) :
    cupOneOuterInclusion p q j ≫ SimplexCategory.δ i =
      cupOneOuterInclusion p (q + 1) j ≫
        eqToHom (congrArg SimplexCategory.mk (by omega : p + (q + 1) + 1 = p + q + 1 + 1)) := by
  ext k
  simp only [cupOneOuterInclusion, SimplexCategory.δ,
    SimplexCategory.len_mk, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
    Fin.succAboveOrderEmb_apply, SimplexCategory.eqToHom_toOrderHom]
  by_cases hk : k.val ≤ j.val
  · rw [Fin.succAbove_of_castSucc_lt]
    · change (if k.val ≤ j.val then k.val else k.val + q) =
        (if k.val ≤ j.val then k.val else k.val + (q + 1))
      simp only [ite_eq_left hk]
    · change (if k.val ≤ j.val then k.val else k.val + q) < i.val
      rw [ite_eq_left hk]
      omega
  · rw [Fin.succAbove_of_le_castSucc]
    · change (if k.val ≤ j.val then k.val else k.val + q) + 1 =
        (if k.val ≤ j.val then k.val else k.val + (q + 1))
      simp only [ite_eq_right hk]
      omega
    · change i.val ≤ (if k.val ≤ j.val then k.val else k.val + q)
      rw [ite_eq_right hk]
      omega

/-- An early deleted vertex becomes an early face of the enlarged outer simplex.
Source: constructed here from Steenrod (1947), cup-one face formula.
-/
theorem cupOneOuterInclusion_comp_earlyFace (p q : ℕ) (j : Fin (p + 1)) (i : Fin (p + q + 3))
    (hi : i.val ≤ j.val) :
    cupOneOuterInclusion p q j ≫ SimplexCategory.δ i =
      SimplexCategory.δ (⟨i.val, by omega⟩ : Fin (p + 3)) ≫
        cupOneOuterInclusion (p + 1) q j.succ ≫
        eqToHom (congrArg SimplexCategory.mk (by omega : p + 1 + q + 1 = p + q + 1 + 1)) := by
  ext k
  simp only [cupOneOuterInclusion, SimplexCategory.δ,
    SimplexCategory.len_mk, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
    Fin.succAboveOrderEmb_apply, SimplexCategory.eqToHom_toOrderHom]
  by_cases hk : k.val < i.val
  · rw [Fin.succAbove_of_castSucc_lt, Fin.succAbove_of_castSucc_lt]
    · change (if k.val ≤ j.val then k.val else k.val + q) =
        (if k.val ≤ j.val + 1 then k.val else k.val + q)
      split <;> split <;> omega
    · exact hk
    · change (if k.val ≤ j.val then k.val else k.val + q) < i.val
      split <;> omega
  · rw [Fin.succAbove_of_le_castSucc, Fin.succAbove_of_le_castSucc]
    · change (if k.val ≤ j.val then k.val else k.val + q) + 1 =
        (if k.val + 1 ≤ j.val + 1 then k.val + 1 else k.val + 1 + q)
      split <;> split <;> omega
    · change i.val ≤ k.val
      omega
    · change i.val ≤ (if k.val ≤ j.val then k.val else k.val + q)
      split <;> omega

/-- A late deleted vertex becomes the face with index reduced by the inner gap.
Source: constructed here from Steenrod (1947), cup-one face formula.
-/
theorem cupOneOuterInclusion_comp_lateFace (p q : ℕ) (j : Fin (p + 1)) (i : Fin (p + q + 3))
    (hi : j.val + q + 1 < i.val) :
    cupOneOuterInclusion p q j ≫ SimplexCategory.δ i =
      SimplexCategory.δ (⟨i.val - q, by omega⟩ : Fin (p + 3)) ≫
        cupOneOuterInclusion (p + 1) q j.castSucc ≫
        eqToHom (congrArg SimplexCategory.mk (by omega : p + 1 + q + 1 = p + q + 1 + 1)) := by
  ext k
  simp only [cupOneOuterInclusion, SimplexCategory.δ,
    SimplexCategory.len_mk, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
    Fin.succAboveOrderEmb_apply, SimplexCategory.eqToHom_toOrderHom]
  by_cases hk : k.val < i.val - q
  · rw [Fin.succAbove_of_castSucc_lt, Fin.succAbove_of_castSucc_lt]
    · rfl
    · exact hk
    · change (if k.val ≤ j.val then k.val else k.val + q) < i.val
      split <;> omega
  · rw [Fin.succAbove_of_le_castSucc, Fin.succAbove_of_le_castSucc]
    · change (if k.val ≤ j.val then k.val else k.val + q) + 1 =
        (if k.val + 1 ≤ j.val then k.val + 1 else k.val + 1 + q)
      split <;> split <;> omega
    · change i.val - q ≤ k.val
      omega
    · change i.val ≤ (if k.val ≤ j.val then k.val else k.val + q)
      split <;> omega



#print axioms cupOneOuterInclusion
#print axioms cupOneInnerInclusion
#print axioms cupOneInnerInclusion_comp_earlyFace
#print axioms cupOneInnerInclusion_comp_lateFace
#print axioms cupOneInnerInclusion_comp_middleFace
#print axioms cupOneOuterInclusion_comp_middleFace
#print axioms cupOneOuterInclusion_comp_earlyFace
#print axioms cupOneOuterInclusion_comp_lateFace

end HodgeLean.Foundations.Singular
