import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.FieldTheory.IsAlgClosed.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Natural multiplication of a rational binomial exponent gives the
corresponding natural power of its series. -/
theorem s2v_l1b_binomial_series_nat_mul
    {K : Type*} [CommRing K] [Algebra ℚ K] (r : ℚ) (n : ℕ) :
    PowerSeries.binomialSeries K ((n : ℚ) * r) =
      PowerSeries.binomialSeries K r ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      PowerSeries.binomialSeries_add, ih, pow_succ]

/-- A characteristic-zero series with constant coefficient one has an
mth root with constant coefficient one for every positive m. -/
theorem s2v_l1b_series_root_of_constant_one
    {K : Type*} [Field K] [CharZero K] (u : PowerSeries K)
    (hu : u.constantCoeff = 1) (m : ℕ) (hm : m ≠ 0) :
    ∃ v : PowerSeries K, v.constantCoeff = 1 ∧ v ^ m = u := by
  let b := PowerSeries.binomialSeries K ((m : ℚ)⁻¹)
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hb : b ^ m = 1 + PowerSeries.X := by
    rw [← s2v_l1b_binomial_series_nat_mul]
    rw [mul_inv_cancel₀ hmQ]
    simpa using (PowerSeries.binomialSeries_nat (R := ℚ) (A := K) 1)
  have hs : PowerSeries.HasSubst (u - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by rw [map_sub, hu, map_one, sub_self])
  let v : PowerSeries K := PowerSeries.substAlgHom (R := K) hs b
  refine ⟨v, ?_, ?_⟩
  · dsimp only [v]
    rw [PowerSeries.coe_substAlgHom]
    change MvPowerSeries.constantCoeff (PowerSeries.subst (R := K) (u - 1) b) = 1
    rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero
      (by change PowerSeries.constantCoeff (u - 1) = 0; rw [map_sub, hu, map_one, sub_self])]
    simp [b]
  · change (PowerSeries.substAlgHom hs b) ^ m = u
    rw [← map_pow, hb, map_add, map_one, PowerSeries.substAlgHom_X]
    ring

/-- Over an algebraically closed characteristic-zero field every series unit
has an mth root that is again a series unit. -/
theorem s2v_l1b_series_root_of_constant_ne_zero
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] (u : PowerSeries K)
    (hu : u.constantCoeff ≠ 0) (m : ℕ) (hm : m ≠ 0) :
    ∃ v : PowerSeries K, v.constantCoeff ≠ 0 ∧ v ^ m = u := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq u.constantCoeff (Nat.pos_of_ne_zero hm)
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow hm] at hc
    exact hu hc.symm
  let w := PowerSeries.C u.constantCoeff⁻¹ * u
  have hw : w.constantCoeff = 1 := by
    simp only [w, map_mul, PowerSeries.constantCoeff_C, inv_mul_cancel₀ hu]
  obtain ⟨v, hv, hvpow⟩ := s2v_l1b_series_root_of_constant_one w hw m hm
  refine ⟨PowerSeries.C c * v, ?_, ?_⟩
  · rw [map_mul, PowerSeries.constantCoeff_C, hv, mul_one]
    exact hc0
  · rw [mul_pow, ← map_pow, hc, hvpow]
    change PowerSeries.C u.constantCoeff * (PowerSeries.C u.constantCoeff⁻¹ * u) = u
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hu, map_one, one_mul]

/-- A nonzero series is a parameter power times an mth power of a unit
when the coefficient field is algebraically closed of characteristic zero. -/
theorem s2v_l1b_series_monomial_root_factor
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (f : PowerSeries K) (hf : f ≠ 0) (m : ℕ) (hm : m ≠ 0) :
    ∃ v : PowerSeries K, v.constantCoeff ≠ 0 ∧
      f = PowerSeries.X ^ f.order.toNat * v ^ m := by
  have hu : (PowerSeries.divXPowOrder f).constantCoeff ≠ 0 := by
    rw [PowerSeries.constantCoeff_divXPowOrder]
    exact PowerSeries.coeff_order hf
  obtain ⟨v, hv, hvm⟩ := s2v_l1b_series_root_of_constant_ne_zero
    (PowerSeries.divXPowOrder f) hu m hm
  refine ⟨v, hv, ?_⟩
  rw [hvm]
  exact PowerSeries.X_pow_order_mul_divXPowOrder.symm

end HodgeLean.Foundations.Program
