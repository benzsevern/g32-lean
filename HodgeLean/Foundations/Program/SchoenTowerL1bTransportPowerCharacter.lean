import HodgeLean.Foundations.Program.SchoenTowerL1bKvalFractionCharacter

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A power of the global character measures the weighted order of a rational local expansion. -/
theorem s2v_l1b_transport_cross_power_character_residue
    {K : Type*} [Field K] {ξ : K} {m q k : ℕ}
    (hξ : IsPrimitiveRoot ξ m) (hm : m ≠ 0)
    (F G : PowerSeries K) (hF : F ≠ 0) (hG : G ≠ 0)
    (hcross : PowerSeries.rescale (ξ ^ q) F * G =
      PowerSeries.C (ξ ^ k) * (F * PowerSeries.rescale (ξ ^ q) G)) :
    Int.ModEq (m : ℤ)
      ((q : ℤ) * ((F.order.toNat : ℤ) - (G.order.toNat : ℤ))) (k : ℤ) := by
  have hfl := PowerSeries.coeff_of_lt_order_toNat (φ := F)
  have hgl := PowerSeries.coeff_of_lt_order_toNat (φ := G)
  have hrfl : ∀ j < F.order.toNat, PowerSeries.coeff j (PowerSeries.rescale (ξ ^ q) F) = 0 := by
    intro j hj
    rw [PowerSeries.coeff_rescale, hfl j hj, mul_zero]
  have hrgl : ∀ j < G.order.toNat, PowerSeries.coeff j (PowerSeries.rescale (ξ ^ q) G) = 0 := by
    intro j hj
    rw [PowerSeries.coeff_rescale, hgl j hj, mul_zero]
  have hc := congrArg (PowerSeries.coeff (F.order.toNat + G.order.toNat)) hcross
  rw [PowerSeries.coeff_C_mul,
    s2v_l1b_kval_coeff_mul_at_lower_bounds _ _ _ _ hrfl hgl,
    s2v_l1b_kval_coeff_mul_at_lower_bounds _ _ _ _ hfl hrgl,
    PowerSeries.coeff_rescale, PowerSeries.coeff_rescale] at hc
  have hc' : (ξ ^ q) ^ F.order.toNat *
      (PowerSeries.coeff F.order.toNat F * PowerSeries.coeff G.order.toNat G) =
      (ξ ^ k * (ξ ^ q) ^ G.order.toNat) *
      (PowerSeries.coeff F.order.toNat F * PowerSeries.coeff G.order.toNat G) := by
    calc
      _ = (ξ ^ q) ^ F.order.toNat * PowerSeries.coeff F.order.toNat F *
          PowerSeries.coeff G.order.toNat G := by ring
      _ = _ := hc
      _ = _ := by ring
  have hp := mul_right_cancel₀
    (mul_ne_zero (PowerSeries.coeff_order hF) (PowerSeries.coeff_order hG)) hc'
  rw [← pow_mul, ← pow_mul, ← pow_add] at hp
  have hmod : Int.ModEq (m : ℤ) ((q * F.order.toNat : ℕ) : ℤ)
      ((k + q * G.order.toNat : ℕ) : ℤ) := by
    apply Int.natCast_modEq_iff.mpr
    rw [hξ.eq_orderOf]
    exact (hξ.isOfFinOrder hm).pow_eq_pow_iff_modEq.mp hp
  convert hmod.sub (Int.ModEq.refl ((q * G.order.toNat : ℕ) : ℤ)) using 1 <;>
    push_cast <;> ring

/-- The ramification equation converts the actual power-character calculation to a binomial divisor residue. -/
theorem s2v_l1b_transport_power_character_binomial_residue
    {K : Type*} [Field K] {ξ : K} {m e q k : ℕ}
    (hξ : IsPrimitiveRoot ξ m) (hm : m ≠ 0) (he : e ≠ 0)
    (hme : m = e * q)
    (F G : PowerSeries K) (hF : F ≠ 0) (hG : G ≠ 0)
    (hcross : PowerSeries.rescale (ξ ^ q) F * G =
      PowerSeries.C (ξ ^ k) * (F * PowerSeries.rescale (ξ ^ q) G))
    {v : ℤ}
    (hram : (m : ℤ) * ((F.order.toNat : ℤ) - (G.order.toNat : ℤ)) = (e : ℤ) * v) :
    Int.ModEq (m : ℤ) v (k : ℤ) := by
  have hmc : (m : ℤ) = (e : ℤ) * (q : ℤ) := by exact_mod_cast hme
  have hc : (e : ℤ) * v =
      (e : ℤ) * ((q : ℤ) * ((F.order.toNat : ℤ) - (G.order.toNat : ℤ))) := by
    rw [← mul_assoc, ← hmc]
    exact hram.symm
  have hv := mul_left_cancel₀ (by exact_mod_cast he : (e : ℤ) ≠ 0) hc
  rw [hv]
  exact s2v_l1b_transport_cross_power_character_residue hξ hm F G hF hG hcross

end HodgeLean.Foundations.Program
