import HodgeLean.Foundations.QuotientDuality.LocalTraceDefs
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.Euclidean

/-! Uniform bounds on open homology give bounds on relative groups along compact subsets. -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits Topology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem open_homology_compact_support_bound (X : TopCat.{0}) [T2Space X] (N : ℕ)
    (h : ∀ (Z : TopCat.{0}) (j : Z ⟶ X), IsOpenEmbedding j →
      ∀ i, N < i → Subsingleton (Homology ℚ Z i))
    (B : Set X) (hB : IsCompact B) (i : ℕ) (hi : N + 1 < i) :
    Subsingleton (RelativeHomology ℚ (TopPair.ofSubset (X := X) Bᶜ) i) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  let P := TopPair.ofSubset (X := X) Bᶜ
  have hX := h X (𝟙 X) IsOpenEmbedding.id (n + 1) (by omega)
  have hU := h P.snd P.map hB.isClosed.isOpen_compl.isOpenEmbedding_subtypeVal n (by omega)
  exact ModuleCat.subsingleton_of_isZero
    ((relativeSingular_homology_exact_relative P n).isZero_of_both_isZero
      (@ModuleCat.isZero_of_subsingleton ℚ _ _ hX)
      (@ModuleCat.isZero_of_subsingleton ℚ _ _ hU))

#print axioms open_homology_compact_support_bound
end HodgeLean.Foundations.QuotientDuality
