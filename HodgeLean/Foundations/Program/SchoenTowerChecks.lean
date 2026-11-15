import HodgeLean.Foundations.Program.SchoenTowerDefs

/-! # Independent checks of exceptional-preimage conventions
The projection tests retain both legs of the scheme fibre product.
The finite permutation test detects a missing ramification premise.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Restricting a composite uses the same categorical order on the preimage.
Source: the scheme fibre-product universal property. -/
theorem s2b_check_deck_comp {W B E : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (d e : W ⟶ W)
    (hd : d ≫ β = β) (he : e ≫ β = β) :
    s2b_preimageDeck β j d hd ≫ s2b_preimageDeck β j e he =
      s2b_preimageDeck β j (d ≫ e) (by rw [Category.assoc, he, hd]) := by
  apply pullback.hom_ext
  · dsimp [s2b_preimageDeck, s2b_toCover, s2b_toExceptional, s2b_preimage]
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
  · dsimp [s2b_preimageDeck, s2b_toCover, s2b_toExceptional, s2b_preimage]
    simp only [Category.assoc, pullback.lift_snd]

/-- The generator leaves the base point of every exceptional covering fibre unchanged.
Source: Schoen (1988), §2, p. 18, the equivariant exceptional square. -/
theorem s2b_check_deck_base {W B E K : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (p : E ⟶ K)
    (d : W ⟶ W) (hd : d ≫ β = β) :
    s2b_preimageDeck β j d hd ≫ (s2b_toExceptional β j ≫ p) =
      s2b_toExceptional β j ≫ p := by
  rw [← Category.assoc]
  exact congrArg (fun f => f ≫ p) (pullback.lift_snd _ _ _)

/-- A free two-sheet permutation has a nonzero primitive-character function.
Source: the regular representation of the cyclic group of order two;
G32 v0.16, §4.1, Lemma 4.3 requires nontrivial branch inertia. -/
theorem s2b_check_unbranched_character :
    let v : Fin 2 → ℂ := ![1, -1]
    v ≠ 0 ∧ (fun i => v (Equiv.swap 0 1 i)) = (-1 : ℂ) • v := by
  dsimp only
  constructor
  · intro hv
    have : (1 : ℂ) = 0 := congrFun hv 0
    exact one_ne_zero this
  · funext i
    fin_cases i <;> norm_num [Equiv.swap_apply_def]

#print axioms s2b_check_deck_comp
#print axioms s2b_check_deck_base
#print axioms s2b_check_unbranched_character
end HodgeLean.Foundations.Program
