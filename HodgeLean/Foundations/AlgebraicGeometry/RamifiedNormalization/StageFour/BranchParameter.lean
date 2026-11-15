import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ComponentSelector
import Mathlib.Data.Int.GCD

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Bezout exponents recover a parameter of a coprime binomial branch in its original field. -/
theorem binomial_bezout_parameter_power
    {K : Type*} [Field K] (n a : ℕ) (hcop : n.Coprime a)
    (s w q : K) (hs : s ≠ 0) (hw : w ^ n = q * s ^ a) :
    (s ^ Nat.gcdA n a * w ^ Nat.gcdB n a) ^ n = q ^ Nat.gcdB n a * s := by
  let A := Nat.gcdA n a
  let B := Nat.gcdB n a
  have hab : (n : ℤ) * A + (a : ℤ) * B = 1 := by
    simpa only [hcop.gcd_eq_one, Nat.cast_one] using (Nat.gcd_eq_gcd_ab n a).symm
  have hcomm (x : K) (b : ℤ) : (x ^ b) ^ n = (x ^ n) ^ b := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm b, zpow_mul, zpow_natCast]
  change (s ^ A * w ^ B) ^ n = q ^ B * s
  rw [mul_pow, hcomm, hcomm, hw, mul_zpow]
  rw [← zpow_natCast s n, ← zpow_mul, ← zpow_natCast s a, ← zpow_mul]
  calc
    s ^ ((n : ℤ) * A) * (q ^ B * s ^ ((a : ℤ) * B)) =
        q ^ B * (s ^ ((n : ℤ) * A) * s ^ ((a : ℤ) * B)) := by ring
    _ = q ^ B * s ^ ((n : ℤ) * A + (a : ℤ) * B) := by rw [zpow_add₀ hs]
    _ = q ^ B * s := by rw [hab, zpow_one]

/-- The explicit Bezout parameter supplies the coprime power equation. -/
theorem binomial_bezout_parameter
    {K : Type*} [Field K] (n a : ℕ) (hcop : n.Coprime a)
    (s w q : K) (hs : s ≠ 0) (hw : w ^ n = q * s ^ a) :
    ∃ t : K, t ^ n = q ^ Nat.gcdB n a * s := by
  exact ⟨s ^ Nat.gcdA n a * w ^ Nat.gcdB n a,
    binomial_bezout_parameter_power n a hcop s w q hs hw⟩

/-- The coprime branch parameter is integral, and every complex evaluation has the power projection. -/
theorem binomial_integral_parameter
    {A K : Type} [CommRing A] [Field K] (F : A →+* K)
    (n a : ℕ) (hn : 0 < n) (hcop : n.Coprime a)
    (s : A) (hs : F s ≠ 0) (w q : normalizedChart F) (hq : IsUnit q)
    (hw : w ^ n = q * StageTwo.integralCoeff F s ^ a) :
    ∃ t b : normalizedChart F,
      (b : K) = (q : K) ^ Nat.gcdB n a ∧ IsUnit b ∧
      t ^ n = b * StageTwo.integralCoeff F s ∧
      ∀ ev : normalizedChart F →+* ℂ,
        ev (StageTwo.integralCoeff F s) = (ev b)⁻¹ * ev t ^ n := by
  let B := Nat.gcdB n a
  let b : normalizedChart F := ⟨(q : K) ^ B, normalizedChart_unit_zpow F q hq B⟩
  let c : normalizedChart F := ⟨(q : K) ^ (-B), normalizedChart_unit_zpow F q hq (-B)⟩
  have hq0 : (q : K) ≠ 0 := (hq.map (normalizedChart F).subtype).ne_zero
  have hb : IsUnit b := by
    apply IsUnit.of_mul_eq_one c
    apply Subtype.ext
    change (q : K) ^ B * (q : K) ^ (-B) = 1
    rw [← zpow_add₀ hq0, add_neg_cancel, zpow_zero]
  have hwe : (w : K) ^ n = (q : K) * F s ^ a := by
    exact congrArg (fun z : normalizedChart F => (z : K)) hw
  obtain ⟨z, hz⟩ := binomial_bezout_parameter n a hcop (F s) (w : K) (q : K) hs hwe
  have hint : z ∈ normalizedChart F := by
    letI := F.toAlgebra
    change _root_.IsIntegral A z
    apply IsIntegral.of_pow hn
    rw [hz]
    exact (b * StageTwo.integralCoeff F s).property
  let t : normalizedChart F := ⟨z, hint⟩
  have ht : t ^ n = b * StageTwo.integralCoeff F s := by
    apply Subtype.ext
    exact hz
  refine ⟨t, b, rfl, hb, ht, ?_⟩
  intro ev
  have he := congrArg ev ht
  simp only [map_pow, map_mul] at he
  have hb0 : ev b ≠ 0 := (hb.map ev).ne_zero
  rw [he, ← mul_assoc, inv_mul_cancel₀ hb0, one_mul]


/-- The same Bezout parameter reconstructs the original divided generator. -/
theorem binomial_bezout_reconstruction
    {K : Type*} [Field K] (n a : ℕ) (hcop : n.Coprime a)
    (s w q : K) (hw0 : w ≠ 0) (hw : w ^ n = q * s ^ a) :
    (s ^ Nat.gcdA n a * w ^ Nat.gcdB n a) ^ a * q ^ Nat.gcdA n a = w := by
  let A := Nat.gcdA n a
  let B := Nat.gcdB n a
  have hab : (n : ℤ) * A + (a : ℤ) * B = 1 := by
    simpa only [hcop.gcd_eq_one, Nat.cast_one] using (Nat.gcd_eq_gcd_ab n a).symm
  have hcomm (x : K) (b : ℤ) : (x ^ b) ^ a = (x ^ a) ^ b := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm b, zpow_mul, zpow_natCast]
  change (s ^ A * w ^ B) ^ a * q ^ A = w
  calc
    (s ^ A * w ^ B) ^ a * q ^ A = ((s ^ a) ^ A * q ^ A) * (w ^ a) ^ B := by
      rw [mul_pow, hcomm, hcomm]
      ring
    _ = (q * s ^ a) ^ A * (w ^ a) ^ B := by rw [mul_zpow]; ring
    _ = (w ^ n) ^ A * (w ^ a) ^ B := by rw [← hw]
    _ = w ^ ((n : ℤ) * A + (a : ℤ) * B) := by
      rw [← zpow_natCast w n, ← zpow_mul, ← zpow_natCast w a, ← zpow_mul,
        zpow_add₀ hw0]
    _ = w := by rw [hab, zpow_one]

end AlgebraicGeometry.RamifiedNormalization.StageFour
