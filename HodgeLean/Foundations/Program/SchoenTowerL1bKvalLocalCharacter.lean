import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.Int.ModEq

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A nonzero coefficient of a rotation eigenseries has the prescribed character residue. -/
theorem s2v_l1b_kval_eigenseries_coefficient_residue
    {K : Type*} [Field K] {ζ : K} {m k n : ℕ}
    (hζ : IsPrimitiveRoot ζ m) (hm : m ≠ 0) (f : PowerSeries K)
    (heigen : PowerSeries.rescale ζ f = PowerSeries.C (ζ ^ k) * f)
    (hn : PowerSeries.coeff n f ≠ 0) :
    Int.ModEq (m : ℤ) (n : ℤ) (k : ℤ) := by
  have hc := congrArg (PowerSeries.coeff n) heigen
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul] at hc
  have he : ζ ^ n = ζ ^ k := mul_right_cancel₀ hn hc
  apply Int.natCast_modEq_iff.mpr
  rw [hζ.eq_orderOf]
  exact (hζ.isOfFinOrder hm).pow_eq_pow_iff_modEq.mp he

/-- The vanishing order of a nonzero rotation eigenseries has its character residue. -/
theorem s2v_l1b_kval_eigenseries_order_residue
    {K : Type*} [Field K] {ζ : K} {m k : ℕ}
    (hζ : IsPrimitiveRoot ζ m) (hm : m ≠ 0) (f : PowerSeries K) (hf : f ≠ 0)
    (heigen : PowerSeries.rescale ζ f = PowerSeries.C (ζ ^ k) * f) :
    Int.ModEq (m : ℤ) (f.order.toNat : ℤ) (k : ℤ) :=
  s2v_l1b_kval_eigenseries_coefficient_residue hζ hm f heigen
    (PowerSeries.coeff_order hf)

/-- Subtracting the orders of two eigenseries allows poles in a local rational presentation. -/
theorem s2v_l1b_kval_eigenseries_fraction_residue
    {K : Type*} [Field K] {ζ : K} {m k l : ℕ}
    (hζ : IsPrimitiveRoot ζ m) (hm : m ≠ 0)
    (f g : PowerSeries K) (hf : f ≠ 0) (hg : g ≠ 0)
    (hef : PowerSeries.rescale ζ f = PowerSeries.C (ζ ^ k) * f)
    (heg : PowerSeries.rescale ζ g = PowerSeries.C (ζ ^ l) * g) :
    Int.ModEq (m : ℤ) ((f.order.toNat : ℤ) - (g.order.toNat : ℤ))
      ((k : ℤ) - (l : ℤ)) :=
  (s2v_l1b_kval_eigenseries_order_residue hζ hm f hf hef).sub
    (s2v_l1b_kval_eigenseries_order_residue hζ hm g hg heg)

end HodgeLean.Foundations.Program
