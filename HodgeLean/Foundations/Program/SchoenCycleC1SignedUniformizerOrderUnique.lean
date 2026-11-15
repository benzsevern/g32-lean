import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Lean.Elab.Tactic.Omega

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program

/-- Two exact signed unit factorizations in the same original uniformizer
have the same integer order. -/
theorem s2e_c1_signed_uniformizer_order_unique
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    (φ : R →+* K) (hφ : Function.Injective φ) (p : R) (hp : Irreducible p)
    (u v : Rˣ) (n m : ℤ)
    (heq : φ (u : R) * φ p ^ n = φ (v : R) * φ p ^ m) : n = m := by
  let k : ℤ := max (-n) (-m)
  have hnk : 0 ≤ n + k := by dsimp [k]; omega
  have hmk : 0 ≤ m + k := by dsimp [k]; omega
  have hpφ : φ p ≠ 0 := fun h => hp.ne_zero (hφ (h.trans (map_zero φ).symm))
  have he : (u : R) * p ^ (n + k).toNat = (v : R) * p ^ (m + k).toNat := by
    apply hφ
    rw [map_mul, map_mul, map_pow, map_pow, ← zpow_natCast, ← zpow_natCast,
      Int.toNat_of_nonneg hnk, Int.toNat_of_nonneg hmk,
      zpow_add₀ hpφ, zpow_add₀ hpφ, ← mul_assoc, ← mul_assoc, heq]
  have hval := congrArg (IsDiscreteValuationRing.addVal R) he
  rw [IsDiscreteValuationRing.addVal_def' u hp,
    IsDiscreteValuationRing.addVal_def' v hp] at hval
  have hnat : (n + k).toNat = (m + k).toNat := ENat.coe_inj.mp hval
  omega

end HodgeLean.Foundations.Program
