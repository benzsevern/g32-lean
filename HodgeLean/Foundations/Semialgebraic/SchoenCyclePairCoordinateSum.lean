import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairVertexCoordinates

/-! Finite sums of global coordinates reduce to the coordinates of any containing face.
HC no distance; AV milestone no distance. -/
noncomputable section
open HodgeLean.Foundations.Program
namespace Semialgebraic.CompatibleTriangulation.Helpers

/-- Extending simplex coordinates by zero preserves every sum with zero constant terms. -/
theorem s2e_pair_coordinate_sum {E M : Type*} [DecidableEq E] [AddCommMonoid M]
    (V s : Finset E) (hsV : s ⊆ V) (w : s → ℝ) (c : E → ℝ)
    (hc : ∀ a, c a = if ha : a ∈ s then w ⟨a, ha⟩ else 0)
    (F : E → ℝ → M) (hF : ∀ a, F a 0 = 0) :
    (∑ a ∈ V, F a (c a)) = ∑ i : s, F i.val (w i) := by
  classical
  calc
    _ = ∑ a ∈ s, F a (c a) := by
      apply (Finset.sum_subset hsV ?_).symm
      intro a _ has
      rw [hc a, dite_eq_right has, hF]
    _ = ∑ i : s, F i.val (c i.val) := (Finset.sum_coe_sort s _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hc i.val, dite_eq_left i.property]

end Semialgebraic.CompatibleTriangulation.Helpers
