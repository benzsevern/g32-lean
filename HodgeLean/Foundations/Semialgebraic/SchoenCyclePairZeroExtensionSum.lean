import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairCoordinateSum

/-! Sums of zero-extended weights over finite vertex subtypes.
HC no distance; AV milestone no distance. -/
noncomputable section
open HodgeLean.Foundations.Program
namespace Semialgebraic.CompatibleTriangulation.Helpers

/-- Zero extension between finite vertex sets preserves weighted sums. -/
theorem s2e_pair_zero_extension_sum {E M : Type*} [DecidableEq E] [AddCommMonoid M]
    (V s : Finset E) (hsV : s ⊆ V) (w : V → ℝ) (u : s → ℝ)
    (hw : ∀ a : V, w a = if ha : a.val ∈ s then u ⟨a.val, ha⟩ else 0)
    (F : E → ℝ → M) (hF : ∀ a, F a 0 = 0) :
    (∑ a : V, F a.val (w a)) = ∑ i : s, F i.val (u i) := by
  classical
  let c : E → ℝ := fun a => if ha : a ∈ V then w ⟨a, ha⟩ else 0
  have hcV (a : V) : c a.val = w a := dite_eq_left a.property
  have hcs (a : E) : c a = if ha : a ∈ s then u ⟨a, ha⟩ else 0 := by
    by_cases haV : a ∈ V
    · rw [show c a = w ⟨a, haV⟩ from dite_eq_left haV]
      exact hw ⟨a, haV⟩
    · have has : a ∉ s := fun ha => haV (hsV ha)
      rw [show c a = 0 from dite_eq_right haV, dite_eq_right has]
  calc
    _ = ∑ a : V, F a.val (c a.val) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hcV a]
    _ = ∑ a ∈ V, F a (c a) := Finset.sum_coe_sort V (fun a => F a (c a))
    _ = _ := s2e_pair_coordinate_sum V s hsV u c hcs F hF

end Semialgebraic.CompatibleTriangulation.Helpers
