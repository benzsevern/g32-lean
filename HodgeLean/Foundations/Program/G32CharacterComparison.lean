import HodgeLean.Foundations.Program.G32CharacterComparisonProofs

/-! Implication from the packed supplier certificates and the open finite class
and restriction statements to the literal 51-row character comparison.
HC no distance; AV milestone no distance. -/
noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory HodgeLean.Papers
set_option maxHeartbeats 400000

/-- The supplier and representation comparison used by `g32c_weilLine_algebraic`
and by the frozen `g32h46_line`, `g32h46_fiber`, and `g32h46_prop46` inputs.
Source: G32 v0.16, Proposition 4.6, Appendix A and Appendix B. -/
theorem g32cc_character_comparison : ∃ (S : Fin 51 → g32p_Supplier) (χc : ∀ i, (S i).H →* ℂˣ)
      (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G),
      (∀ j, Simple (τ j) ∧ Simple (τbar j) ∧ ¬ g32p_SelfDual (τ j) ∧
        (∀ g, (τbar j).character g = star ((τ j).character g)) ∧ 0 < g32p_cwMult (τ j)) ∧
      (∀ j, Simple (θ j) ∧ g32p_Quaternionic (θ j) ∧ 0 < g32p_cwMult (θ j)) ∧
      (∀ j k, j ≠ k → IsEmpty (τ j ≅ τ k) ∧ IsEmpty (τ j ≅ τbar k)) ∧
      (∀ j k : Fin 4, j ≠ k → IsEmpty (θ j ≅ θ k)) ∧
      Nonempty (τ 2 ≅ g32p_rho) ∧
      (∀ σ : FDRep ℂ g32p_G, Simple σ → 0 < g32p_cwMult σ →
        (¬ g32p_SelfDual σ → ∃ j, Nonempty (σ ≅ τ j) ∨ Nonempty (σ ≅ τbar j)) ∧
        (g32p_Quaternionic σ → ∃ j, Nonempty (σ ≅ θ j))) ∧
      ∀ i : Fin 51,
        (∀ h, ((χc i h : ℂˣ) : ℂ) =
          g32p_root (S i).m ^ (Multiplicative.toAdd ((S i).χ h)).val) ∧
        (∃ r ∈ g32WitnessTable, r.i = i.val + 1 ∧ r.m = (S i).m ∧
          r.orderH = Nat.card (S i).H ∧ (g32p_exponents (S i)).Perm (expandExps r.exps)) ∧
        ∃ v ∈ g32VectorTable, v.i = i.val + 1 ∧
          papersA τ τbar θ (S i).H (χc i) = g32SparseVec v.coords :=
  g32cc_character_comparison_aux

end HodgeLean.Foundations.Program
