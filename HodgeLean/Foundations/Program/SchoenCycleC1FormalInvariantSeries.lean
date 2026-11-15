import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Formal series fixed by a primitive coordinate rotation -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A series fixed by a primitive rotation is uniquely a series in the
corresponding power of the coordinate. -/
theorem s2e_c1_invariant_series_unique_expansion
    {k : Type*} [CommRing k] [IsDomain k] (d : ℕ) (hd : d ≠ 0)
    (ζ : k) (hζ : IsPrimitiveRoot ζ d) (f : PowerSeries k) :
    PowerSeries.rescale ζ f = f ↔
      ∃! g : PowerSeries k, PowerSeries.expand d hd g = f := by
  constructor
  · intro hf
    have hz (n : ℕ) (hn : ¬ d ∣ n) : f.coeff n = 0 := by
      by_contra hc
      have he := congrArg (PowerSeries.coeff n) hf
      rw [PowerSeries.coeff_rescale] at he
      have hp : ζ ^ n = 1 := mul_right_cancel₀ hc (he.trans (one_mul _).symm)
      exact hn ((hζ.pow_eq_one_iff_dvd n).mp hp)
    refine ⟨PowerSeries.mk (fun n => f.coeff (d * n)), ?_, ?_⟩
    · ext n
      rw [PowerSeries.coeff_expand]
      split_ifs with hn
      · rw [PowerSeries.coeff_mk, Nat.mul_div_cancel' hn]
      · exact (hz n hn).symm
    · intro g hg
      ext n
      have he := congrArg (PowerSeries.coeff (d * n)) hg
      simpa only [PowerSeries.coeff_expand_mul, PowerSeries.coeff_mk] using he
  · rintro ⟨g, rfl, _⟩
    ext n
    rw [PowerSeries.coeff_rescale]
    by_cases hn : d ∣ n
    · rw [(hζ.pow_eq_one_iff_dvd n).mpr hn, one_mul]
    · rw [PowerSeries.coeff_expand_of_not_dvd d hd g hn, mul_zero]

end HodgeLean.Foundations.Program
