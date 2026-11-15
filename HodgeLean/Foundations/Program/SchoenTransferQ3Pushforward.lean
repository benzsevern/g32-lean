import HodgeLean.Foundations.Program.SchoenTransferDefs

/-! Residue degrees in the retained cycle pushforward. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- Constant codimension weights retain every residue degree, for any cycle
on a compact source. -/
theorem s4_q3_constant_weight_pushforward
    {X W : Scheme} [CompactSpace X] (q : X ⟶ W) [QuasiCompact q]
    (k : ℕ) (γ : AlgebraicCycle X ℚ) :
    AlgebraicCycle.map q (fun _ => k) (fun _ => k) γ =
      ∑ᶠ y : X, Function.locallyFinsuppWithin.single (q y)
        ((q.residueDegree y : ℚ) * γ y) := by
  classical
  have hsupport : (Function.support (fun y : X =>
      Function.locallyFinsuppWithin.single (q y)
        ((q.residueDegree y : ℚ) * γ y))) ⊆ γ.support := by
    intro y hy
    by_contra hn
    have hz : γ y = 0 := not_not.mp hn
    apply hy
    change Function.locallyFinsuppWithin.single (q y)
      ((q.residueDegree y : ℚ) * γ y) = 0
    rw [hz, mul_zero, Function.locallyFinsuppWithin.single_zero]
  rw [finsum_eq_sum_of_support_subset _
    (fun y hy => γ.finite_support.mem_toFinset.mpr (hsupport hy))]
  ext z
  simp only [AlgebraicCycle.map, Function.locallyFinsupp.map_apply,
    Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
    Function.locallyFinsuppWithin.single_apply]
  rw [finsum_mem_def,
    finsum_eq_finsetSum_of_support_subset (s := γ.finite_support.toFinset)]
  · apply Finset.sum_congr rfl
    intro y hy
    by_cases hf : q y = z
    · subst z
      simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff,
        ↓reduceIte, AlgebraicCycle.mapCoeff, mul_comm]
    · simp [hf, Ne.symm hf]
  · intro y hy
    apply γ.finite_support.mem_toFinset.mpr
    by_contra hn
    have hz : γ y = 0 := not_not.mp hn
    simp [hz] at hy

end HodgeLean.Foundations.Program
