import Mathlib.Data.Complex.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The original generator detects nonzero parameters, while the selector and inertia detect the zero parameter, making the binomial coordinates injective. -/
theorem binomial_orbit_coordinates_injective
    {X B : Type*} (d : X → X) (p : X → B) (Q T W : X → ℂ)
    (m g a : ℕ) (A : ℤ) (ζ ξ : ℂ)
    (hζ : IsPrimitiveRoot ζ m) (hξ : IsPrimitiveRoot ξ g)
    (hQ : ∀ x, Q x ≠ 0)
    (hW : ∀ x, W x = T x ^ a * Q x ^ A)
    (hbase : ∀ x y, Q x = Q y → T x = T y → p x = p y)
    (horbit : ∀ x y, p x = p y → ∃ k : ℕ, d^[k] x = y)
    (hperiod : ∀ x, d^[m] x = x)
    (hinertia : ∀ x, T x = 0 → d^[g] x = x)
    (hWeigen : ∀ k x, W (d^[k] x) = ζ ^ k * W x)
    (hQeigen : ∀ k x, Q (d^[k] x) = ξ ^ k * Q x) :
    Function.Injective (fun x => (Q x, T x)) := by
  intro x y hxy
  have hQxy := congrArg Prod.fst hxy
  have hTxy := congrArg Prod.snd hxy
  dsimp only at hQxy hTxy
  obtain ⟨k, hk⟩ := horbit x y (hbase x y hQxy hTxy)
  have fixed_of_dvd (N : ℕ) (hN : d^[N] x = x) (hNk : N ∣ k) : d^[k] x = x := by
    have hp : Function.IsPeriodicPt d N x := hN
    obtain ⟨l, rfl⟩ := hNk
    exact hp.mul_const l
  have hfix : d^[k] x = x := by
    by_cases ht : T x = 0
    · apply fixed_of_dvd g (hinertia x ht)
      apply (hξ.pow_eq_one_iff_dvd k).mp
      apply mul_right_cancel₀ (hQ x)
      have he := hQeigen k x
      rw [hk, ← hQxy] at he
      simpa only [one_mul] using he.symm
    · apply fixed_of_dvd m (hperiod x)
      apply (hζ.pow_eq_one_iff_dvd k).mp
      have hw0 : W x ≠ 0 := by
        rw [hW]
        exact mul_ne_zero (pow_ne_zero a ht) (zpow_ne_zero A (hQ x))
      have hWxy : W x = W y := by rw [hW x, hW y, hQxy, hTxy]
      apply mul_right_cancel₀ hw0
      have he := hWeigen k x
      rw [hk, ← hWxy] at he
      simpa only [one_mul] using he.symm
  exact hfix.symm.trans hk

end AlgebraicGeometry.RamifiedNormalization.StageFour
