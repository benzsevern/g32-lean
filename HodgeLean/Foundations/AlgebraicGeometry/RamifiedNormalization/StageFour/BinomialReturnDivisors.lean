import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.BinomialOrbitInjectivity

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The selector and original generator give the exact return divisor at zero and at every nonzero branch parameter. -/
theorem binomial_coordinate_return_divisor
    {X : Type*} (d : X → X) (Q T W : X → ℂ)
    (m g a : ℕ) (A : ℤ) (ζ ξ : ℂ)
    (hζ : IsPrimitiveRoot ζ m) (hξ : IsPrimitiveRoot ξ g)
    (hQ : ∀ x, Q x ≠ 0) (hW : ∀ x, W x = T x ^ a * Q x ^ A)
    (hperiod : ∀ x, d^[m] x = x)
    (hinertia : ∀ x, T x = 0 → d^[g] x = x)
    (hWeigen : ∀ k x, W (d^[k] x) = ζ ^ k * W x)
    (hQeigen : ∀ k x, Q (d^[k] x) = ξ ^ k * Q x) :
    ∀ x k, d^[k] x = x ↔ (if T x = 0 then g else m) ∣ k := by
  intro x k
  have hdetect (V : X → ℂ) (c : ℂ) (N : ℕ) (hV : V x ≠ 0)
      (hc : IsPrimitiveRoot c N) (hfix : d^[N] x = x)
      (heigen : ∀ k, V (d^[k] x) = c ^ k * V x) :
      d^[k] x = x ↔ N ∣ k := by
    constructor
    · intro h
      apply (hc.pow_eq_one_iff_dvd k).mp
      apply mul_right_cancel₀ hV
      have he := heigen k
      rw [h] at he
      simpa only [one_mul] using he.symm
    · rintro ⟨l, rfl⟩
      have hp : Function.IsPeriodicPt d N x := hfix
      exact hp.mul_const l
  by_cases ht : T x = 0
  · rw [if_pos ht]
    exact hdetect Q ξ g (hQ x) hξ (hinertia x ht) (fun k => hQeigen k x)
  · rw [if_neg ht]
    have hw0 : W x ≠ 0 := by
      rw [hW x]
      exact mul_ne_zero (pow_ne_zero a ht) (zpow_ne_zero A (hQ x))
    exact hdetect W ζ m hw0 hζ (hperiod x) (fun k => hWeigen k x)

end AlgebraicGeometry.RamifiedNormalization.StageFour
