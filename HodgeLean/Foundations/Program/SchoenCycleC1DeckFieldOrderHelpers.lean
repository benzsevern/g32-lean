import Mathlib.FieldTheory.Fixed
import HodgeLean.Foundations.Program.SchoenCycleC1FunctionFieldActionHelpers
import Mathlib.GroupTheory.OrderOfElement

/-! # Exact orders retained in the generic deck representation -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A scheme deck generator's period and exclusion of shorter returns give
its exact order in the actual function-field representation. -/
theorem s2e_c1_deck_field_order
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsSeparated f]
    (φ : Y.functionField →+* X.functionField)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ f)
    (u : Aut (Over.mk f)) (m : ℕ) (hm : 0 < m)
    (hpow : End.of u.asIso.hom.left ^ m = 1)
    (hfaith : ∀ n, n < m → End.of u.asIso.hom.left ^ n = 1 → n = 0) :
    orderOf (s2e_c1_deckFunctionFieldHom f φ hφ u) = m := by
  let F : Aut (Over.mk f) →* End X := {
    toFun := fun v => End.of v.asIso.hom.left
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hF : Function.Injective F := by
    intro a b hab
    apply Aut.ext
    apply Iso.ext
    apply Over.OverMorphism.ext
    exact congrArg End.asHom hab
  have horder : orderOf u = m := by
    apply (orderOf_eq_iff hm).mpr
    constructor
    · apply hF
      rw [map_pow, map_one]
      change End.of u.asIso.hom.left ^ m = 1
      exact hpow
    · intro n hn hnpos hret
      have he := congrArg F hret
      simp only [map_pow, map_one] at he
      exact (Nat.ne_of_gt hnpos) (hfaith n hn he)
  rw [orderOf_injective _ (s2e_c1_deckFunctionFieldHom_injective f φ hφ)]
  exact horder

/-- The faithful scheme deck period bounds the degree of the actual
finite generic extension from below. -/
theorem s2e_c1_deck_period_le_fieldDegree
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsSeparated f]
    (φ : Y.functionField →+* X.functionField)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ f)
    (u : Aut (Over.mk f)) (m : ℕ) (hm : 0 < m)
    (hpow : End.of u.asIso.hom.left ^ m = 1)
    (hfaith : ∀ n, n < m → End.of u.asIso.hom.left ^ n = 1 → n = 0) :
    letI := φ.toAlgebra
    ∀ [Module.Finite Y.functionField X.functionField],
      m ≤ Module.finrank Y.functionField X.functionField := by
  letI := φ.toAlgebra
  intro hfin
  have horder := s2e_c1_deck_field_order f φ hφ u m hm hpow hfaith
  calc
    m = orderOf (s2e_c1_deckFunctionFieldHom f φ hφ u) := horder.symm
    _ ≤ Nat.card (X.functionField ≃ₐ[Y.functionField] X.functionField) := orderOf_le_card
    _ ≤ Module.finrank Y.functionField X.functionField := by
      simpa only [Nat.card_eq_fintype_card] using
        (AlgEquiv.card_le (F := Y.functionField) (K := X.functionField))

end HodgeLean.Foundations.Program
