import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Group.Units.Hom

/-! # Uniqueness of signed parameter orders in the actual fraction field -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Two local-unit decompositions of a rational function in one DVR
parameter have the same signed order, including when both have poles. -/
theorem s2e_c1_signed_dvr_order_unique
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (t : R) (ht : Irreducible t) (u v : Rˣ) (r s : ℤ)
    (h : algebraMap R K (u : R) * algebraMap R K t ^ r =
      algebraMap R K (v : R) * algebraMap R K t ^ s) : r = s := by
  have htK : algebraMap R K t ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne ht.ne_zero
  let N : ℤ := max (-r) (-s)
  have hr : 0 ≤ r + N := by dsimp only [N]; omega
  have hs : 0 ≤ s + N := by dsimp only [N]; omega
  have he : algebraMap R K ((u : R) * t ^ (r + N).toNat) =
      algebraMap R K ((v : R) * t ^ (s + N).toNat) := by
    simpa only [map_mul, map_pow, ← zpow_natCast, Int.toNat_of_nonneg hr,
      Int.toNat_of_nonneg hs, zpow_add₀ htK, ← mul_assoc] using
      congrArg (fun a : K => a * algebraMap R K t ^ N) h
  have hn := IsDiscreteValuationRing.unit_mul_pow_congr_pow ht ht u v
    (r + N).toNat (s + N).toNat ((IsFractionRing.injective R K) he)
  have hi := congrArg (fun a : ℕ => (a : ℤ)) hn
  rw [Int.toNat_of_nonneg hr, Int.toNat_of_nonneg hs] at hi
  omega

end HodgeLean.Foundations.Program
