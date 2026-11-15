import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairCoordinateSum

/-! Restriction of barycentric coordinates to their finite supporting vertex set.
HC no distance; AV milestone no distance. -/
noncomputable section
open HodgeLean.Foundations.Program
namespace Semialgebraic.CompatibleTriangulation.Helpers

/-- Weights supported on a subset are the zero extension of actual simplex weights on it. -/
theorem s2e_pair_restrict_weights {E : Type*} [DecidableEq E]
    (V s : Finset E) (hsV : s ⊆ V) (w : stdSimplex ℝ V)
    (hsupport : ∀ a : V, a.val ∉ s → w.val a = 0) :
    ∃ u : stdSimplex ℝ s,
      ∀ a : V, w.val a = if ha : a.val ∈ s then u.val ⟨a.val, ha⟩ else 0 := by
  classical
  let f : E → ℝ := fun a => if ha : a ∈ V then w.val ⟨a, ha⟩ else 0
  have hf (a : V) : f a.val = w.val a := by
    exact dite_eq_left a.property
  have htotal : ∑ a ∈ s, f a = 1 := by
    calc
      _ = ∑ a ∈ V, f a := by
        apply Finset.sum_subset hsV
        intro a ha has
        rw [show f a = w.val ⟨a, ha⟩ from dite_eq_left ha]
        exact hsupport ⟨a, ha⟩ has
      _ = ∑ a : V, w.val a := by
        rw [← Finset.sum_coe_sort V f]
        exact Finset.sum_congr rfl (fun a _ => hf a)
      _ = 1 := w.property.2
  let u : stdSimplex ℝ s := ⟨fun a => f a.val, by
    constructor
    · intro a
      change 0 ≤ f a.val
      rw [show f a.val = w.val ⟨a.val, hsV a.property⟩ from dite_eq_left (hsV a.property)]
      exact w.property.1 _
    · rw [Finset.sum_coe_sort s f]
      exact htotal⟩
  refine ⟨u, ?_⟩
  intro a
  by_cases ha : a.val ∈ s
  · rw [dite_eq_left ha]
    exact (hf a).symm
  · rw [dite_eq_right ha]
    exact hsupport a ha

end Semialgebraic.CompatibleTriangulation.Helpers
