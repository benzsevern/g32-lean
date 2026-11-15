import HodgeLean.Foundations.QuotientDuality.RetainedCycleWeightedCarrier

/-! Fibrewise collection of literal supported representatives. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
open scoped BigOperators Classical
namespace HodgeLean.Foundations.QuotientDuality

/-- A finite family drawn from fixed supported representatives descends to any carrier containing
all primes with nonzero total fibre weight. The equality retains the original common support. -/
lemma retained_weighted_descent_of_fibre_representatives
    {I P : Type} [Fintype I] (Y : TopCat.{0}) (n : ℕ)
    (ξ : I → P) (q : I → ℚ) (S : P → Set Y)
    (v : ∀ p, CohomologyWithSupport ℚ Y (S p) n)
    (A T : Set Y) (hAT : A ⊆ T) (hST : ∀ i, S (ξ i) ⊆ T)
    (hSA : ∀ p ∈ Finset.univ.image ξ,
      (∑ i with ξ i = p, q i) ≠ 0 → S p ⊆ A) :
    ∃ b : CohomologyWithSupport ℚ Y A n,
      enlargeSupport ℚ Y hAT n b =
        ∑ i, q i • enlargeSupport ℚ Y (hST i) n (v (ξ i)) := by
  let t := Finset.univ.image ξ
  let w : P → ℚ := fun p => ∑ i with ξ i = p, q i
  have hPT : ∀ p ∈ t, S p ⊆ T := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hST i
  let c : P → CohomologyWithSupport ℚ Y T n := fun p =>
    if hp : p ∈ t then enlargeSupport ℚ Y (hPT p hp) n (v p) else 0
  let b : CohomologyWithSupport ℚ Y A n :=
    ∑ p ∈ t, if hm : p ∈ t then
      if hp : w p ≠ 0 then
        w p • enlargeSupport ℚ Y (hSA p hm hp) n (v p) else 0
      else 0
  have hgroup : (∑ i, q i • enlargeSupport ℚ Y (hST i) n (v (ξ i))) =
      ∑ p ∈ t, w p • c p := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := t)
      (fun i hi => Finset.mem_image_of_mem ξ hi)
      (fun i => q i • enlargeSupport ℚ Y (hST i) n (v (ξ i)))]
    apply Finset.sum_congr rfl
    intro p hp
    calc
      (∑ i with ξ i = p, q i • enlargeSupport ℚ Y (hST i) n (v (ξ i))) =
          ∑ i with ξ i = p, q i • enlargeSupport ℚ Y (hPT p hp) n (v p) := by
        apply Finset.sum_congr rfl
        intro i hi
        have he := (Finset.mem_filter.mp hi).2
        subst p
        rfl
      _ = w p • enlargeSupport ℚ Y (hPT p hp) n (v p) := Finset.sum_smul.symm
      _ = w p • c p := by
        dsimp only [c]
        rw [dite_eq_left hp]
  refine ⟨b, ?_⟩
  rw [hgroup]
  dsimp only [b]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [dite_eq_left hp]
  change _ = w p • c p
  dsimp only [c]
  rw [dite_eq_left hp]
  by_cases hw : w p ≠ 0
  · rw [dite_eq_left hw, map_smul]
    congr 1
    unfold enlargeSupport
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
    rfl
  · rw [dite_eq_right hw, map_zero, not_ne_iff.mp hw, zero_smul]

end HodgeLean.Foundations.QuotientDuality
