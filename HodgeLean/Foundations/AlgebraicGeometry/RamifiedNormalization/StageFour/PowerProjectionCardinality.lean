import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.NonzeroPowerProjectionFibre
import Mathlib.SetTheory.Cardinal.Finite

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The labelled power projection has gcd-many points at zero and label-count times power-degree points elsewhere. -/
theorem weighted_power_fibre_cardinality
    (g n : ℕ) (hg : 0 < g) (hn : 0 < n) (k : ZMod g → ℂ) (hk : ∀ j, k j ≠ 0)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ n) (b : ℂ) :
    Finite {z : ZMod g × ℂ // k z.1 * z.2 ^ n = b} ∧
      Nat.card {z : ZMod g × ℂ // k z.1 * z.2 ^ n = b} =
        if b = 0 then g else g * n := by
  classical
  letI : NeZero g := ⟨Nat.ne_of_gt hg⟩
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  by_cases hb : b = 0
  · subst b
    let E := weightedPowerZeroFibreEquiv g n hn k hk
    refine ⟨Finite.of_equiv _ E.symm, ?_⟩
    rw [if_pos rfl, Nat.card_congr E, Nat.card_zmod]
  · let E := weightedPowerNonzeroFibreEquiv g n hn k hk b hb ζ hζ
    refine ⟨Finite.of_equiv _ E.symm, ?_⟩
    rw [if_neg hb, Nat.card_congr E, Nat.card_prod, Nat.card_zmod, Nat.card_zmod]

end AlgebraicGeometry.RamifiedNormalization.StageFour
