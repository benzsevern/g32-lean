import HodgeLean.Foundations.QuotientDuality.ProperCycleFiniteGoodCoverHomology
import HodgeLean.Foundations.QuotientDuality.ProperCycleBarycentricSplit
import Mathlib.Analysis.Convex.Contractible

/-! # Actual barycentric open stars as a finite good cover -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- A literal barycentric face star is star-convex about any positive normalized point of its selected face, in the actual finite real coordinate space.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric star contractions.
HC no distance; AV milestone no distance. -/
lemma properCycle_barycentric_star_starConvex
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : Set (Finset ι)) (T : Finset ι)
    (p : ProperCycleFacePoint T) :
    StarConvex ℝ p.val.val
      {w : ι → ℝ | w ∈ stdSimplex ℝ ι ∧
        (∃ s ∈ F, ∀ i ∉ s, w i = 0) ∧ ∀ i ∈ T, 0 < w i} := by
  intro w hw a b ha hb hab
  obtain ⟨s, hs, hws⟩ := hw.2.1
  have hTs : T ⊆ s := by
    intro i hi
    by_contra his
    have hp := hw.2.2 i hi
    rw [hws i his] at hp
    exact (lt_irrefl 0) hp
  refine ⟨(convex_stdSimplex ℝ ι) p.val.property hw.1 ha hb hab, ⟨s, hs, ?_⟩, ?_⟩
  · intro i his
    have hpi : p.val.val i = 0 := p.property.2 i (fun hi => his (hTs hi))
    change a * p.val.val i + b * w i = 0
    rw [hpi, hws i his, mul_zero, mul_zero, add_zero]
  · intro i hi
    change 0 < a * p.val.val i + b * w i
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      rw [ha0, hb1, zero_mul, one_mul, zero_add]
      exact hw.2.2 i hi
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) (p.property.1 i hi))
        (mul_nonneg hb (le_of_lt (hw.2.2 i hi)))

/-- Every actual nonempty positive-coordinate face star is contractible, by its explicit star-convex model in the original finite real coordinates.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric open stars.
HC no distance; AV milestone no distance. -/
lemma properCycle_barycentric_star_contractible
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : Set (Finset ι))
    (T : Finset ι) (hT : T.Nonempty)
    (hstar : Nonempty {w : {u : stdSimplex ℝ ι | ∃ s ∈ F, ∀ i ∉ s, u.val i = 0} |
      ∀ i ∈ T, 0 < w.val.val i}) :
    ContractibleSpace {w : {u : stdSimplex ℝ ι | ∃ s ∈ F, ∀ i ∉ s, u.val i = 0} |
      ∀ i ∈ T, 0 < w.val.val i} := by
  let A := {w : {u : stdSimplex ℝ ι | ∃ s ∈ F, ∀ i ∉ s, u.val i = 0} |
    ∀ i ∈ T, 0 < w.val.val i}
  let B := {w : ι → ℝ | w ∈ stdSimplex ℝ ι ∧
    (∃ s ∈ F, ∀ i ∉ s, w i = 0) ∧ ∀ i ∈ T, 0 < w i}
  let E : A ≃ₜ B :=
    { toFun := fun w => ⟨w.val.val.val, w.val.val.property, w.val.property, w.property⟩
      invFun := fun w => ⟨⟨⟨w.val, w.property.1⟩, w.property.2.1⟩, w.property.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let w : A := Classical.choice hstar
  let p : ProperCycleFacePoint T := properCycle_star_face T hT ⟨w.val.val, w.property⟩
  letI : ContractibleSpace B := (properCycle_barycentric_star_starConvex F T p).contractibleSpace
    ⟨(E w).val, (E w).property⟩
  exact E.contractibleSpace

end HodgeLean.Foundations.QuotientDuality
