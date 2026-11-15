import HodgeLean.Foundations.QuotientDuality.RetainedCycleWeightedDescent

/-! Supported representatives indexed by actual fibres. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
open scoped BigOperators Classical
namespace HodgeLean.Foundations.QuotientDuality

/-- Compatible occurrence classes come from one supported representative for each actual fibre. -/
lemma retained_supported_fibre_section
    {I P : Type} (Y : TopCat.{0}) (n : ℕ) (S : P → Set Y) (ξ : I → P)
    (a : ∀ i, CohomologyWithSupport ℚ Y (S (ξ i)) n)
    (ha : ∀ i j, ξ i = ξ j → HEq (a i) (a j)) :
    ∃ v : ∀ p, CohomologyWithSupport ℚ Y (S p) n, ∀ i, v (ξ i) = a i := by
  let v : ∀ p, CohomologyWithSupport ℚ Y (S p) n := fun p =>
    if h : ∃ i, ξ i = p then h.choose_spec ▸ a h.choose else 0
  refine ⟨v, ?_⟩
  intro i
  dsimp only [v]
  rw [dite_eq_left (show ∃ j, ξ j = ξ i from ⟨i, rfl⟩)]
  have ht : ∀ (p q : P) (e : p = q)
      (x : CohomologyWithSupport ℚ Y (S p) n)
      (y : CohomologyWithSupport ℚ Y (S q) n), HEq x y → e ▸ x = y := by
    intro p q e x y h
    subst q
    exact eq_of_heq h
  apply ht
  exact ha _ i (Classical.choose_spec (show ∃ j, ξ j = ξ i from ⟨i, rfl⟩))

/-- Compatible occurrence representatives descend with their exact weighted common-support equality. -/
lemma retained_supported_descent_of_repeats
    {I P : Type} [Fintype I] (Y : TopCat.{0}) (n : ℕ)
    (ξ : I → P) (q : I → ℚ) (S : P → Set Y)
    (a : ∀ i, CohomologyWithSupport ℚ Y (S (ξ i)) n)
    (ha : ∀ i j, ξ i = ξ j → HEq (a i) (a j))
    (A T : Set Y) (hAT : A ⊆ T) (hST : ∀ i, S (ξ i) ⊆ T)
    (hSA : ∀ p ∈ Finset.univ.image ξ,
      (∑ i with ξ i = p, q i) ≠ 0 → S p ⊆ A) :
    ∃ b : CohomologyWithSupport ℚ Y A n,
      enlargeSupport ℚ Y hAT n b =
        ∑ i, q i • enlargeSupport ℚ Y (hST i) n (a i) := by
  obtain ⟨v, hv⟩ := retained_supported_fibre_section Y n S ξ a ha
  obtain ⟨b, hb⟩ := retained_weighted_descent_of_fibre_representatives
    Y n ξ q S v A T hAT hST hSA
  refine ⟨b, hb.trans ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  rw [hv i]

end HodgeLean.Foundations.QuotientDuality
