import HodgeLean.Foundations.Program.SchoenTowerL1bKvalLocalCharacter

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The first possible coefficient of a product uses only the first possible
coefficient of each factor. -/
theorem s2v_l1b_kval_coeff_mul_at_lower_bounds
    {K : Type*} [Field K] (f g : PowerSeries K) (n m : ℕ)
    (hf : ∀ j < n, PowerSeries.coeff j f = 0)
    (hg : ∀ j < m, PowerSeries.coeff j g = 0) :
    PowerSeries.coeff (n + m) (f * g) =
      PowerSeries.coeff n f * PowerSeries.coeff m g := by
  rw [PowerSeries.coeff_mul,
    Finset.sum_eq_single_of_mem (a := (n, m)) (by simp)]
  intro ij hij hne
  rcases trichotomy_of_add_eq_add (Finset.mem_antidiagonal.mp hij) with he | hn | hm
  · exact False.elim (hne (Prod.ext he.1 he.2))
  · rw [hf _ hn, zero_mul]
  · rw [hg _ hm, mul_zero]

/-- A rational eigenfunction has the character residue in any nonzero series
presentation; the two series need not be eigenvectors separately. -/
theorem s2v_l1b_kval_cross_eigenseries_residue
    {K : Type*} [Field K] {ζ : K} {m k : ℕ}
    (hζ : IsPrimitiveRoot ζ m) (hm : m ≠ 0)
    (f g : PowerSeries K) (hf : f ≠ 0) (hg : g ≠ 0)
    (heigen : PowerSeries.rescale ζ f * g =
      PowerSeries.C (ζ ^ k) * (f * PowerSeries.rescale ζ g)) :
    Int.ModEq (m : ℤ) ((f.order.toNat : ℤ) - (g.order.toNat : ℤ)) (k : ℤ) := by
  have hfl := PowerSeries.coeff_of_lt_order_toNat (φ := f)
  have hgl := PowerSeries.coeff_of_lt_order_toNat (φ := g)
  have hrfl : ∀ j < f.order.toNat, PowerSeries.coeff j (PowerSeries.rescale ζ f) = 0 := by
    intro j hj
    rw [PowerSeries.coeff_rescale, hfl j hj, mul_zero]
  have hrgl : ∀ j < g.order.toNat, PowerSeries.coeff j (PowerSeries.rescale ζ g) = 0 := by
    intro j hj
    rw [PowerSeries.coeff_rescale, hgl j hj, mul_zero]
  have hc := congrArg (PowerSeries.coeff (f.order.toNat + g.order.toNat)) heigen
  rw [PowerSeries.coeff_C_mul,
    s2v_l1b_kval_coeff_mul_at_lower_bounds _ _ _ _ hrfl hgl,
    s2v_l1b_kval_coeff_mul_at_lower_bounds _ _ _ _ hfl hrgl,
    PowerSeries.coeff_rescale, PowerSeries.coeff_rescale] at hc
  have hc' : ζ ^ f.order.toNat *
      (PowerSeries.coeff f.order.toNat f * PowerSeries.coeff g.order.toNat g) =
      (ζ ^ k * ζ ^ g.order.toNat) *
      (PowerSeries.coeff f.order.toNat f * PowerSeries.coeff g.order.toNat g) := by
    calc
      _ = ζ ^ f.order.toNat * PowerSeries.coeff f.order.toNat f *
          PowerSeries.coeff g.order.toNat g := by ring
      _ = _ := hc
      _ = _ := by ring
  have hp := mul_right_cancel₀
    (mul_ne_zero (PowerSeries.coeff_order hf) (PowerSeries.coeff_order hg)) hc'
  rw [← pow_add] at hp
  have hmod : Int.ModEq (m : ℤ) (f.order.toNat : ℤ)
      ((k + g.order.toNat : ℕ) : ℤ) := by
    apply Int.natCast_modEq_iff.mpr
    rw [hζ.eq_orderOf]
    exact (hζ.isOfFinOrder hm).pow_eq_pow_iff_modEq.mp hp
  convert hmod.sub (Int.ModEq.refl (g.order.toNat : ℤ)) using 1 <;> push_cast <;> ring

end HodgeLean.Foundations.Program
