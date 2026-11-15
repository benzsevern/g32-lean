import HodgeLean.Foundations.Program.SchoenTowerL1bKvalFractionCharacter
import HodgeLean.Foundations.Program.SchoenTowerL1bKvalRamificationArithmetic

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A rational eigenfunction gives its ramified base residue without requiring
an eigenvector numerator or denominator. -/
theorem s2v_l1b_kval_ramified_fraction_residue
    {K : Type*} [Field K] {ζ : K} {e k : ℕ}
    (hζ : IsPrimitiveRoot ζ e) (he : e ≠ 0)
    (f g : PowerSeries K) (hf : f ≠ 0) (hg : g ≠ 0)
    (heigen : PowerSeries.rescale ζ f * g =
      PowerSeries.C (ζ ^ k) * (f * PowerSeries.rescale ζ g))
    {m q w : ℤ} (hm : m = (e : ℤ) * q)
    (horder : m * ((f.order.toNat : ℤ) - (g.order.toNat : ℤ)) = (e : ℤ) * w) :
    Int.ModEq m w (q * (k : ℤ)) := by
  exact s2v_l1b_kval_ramification_residue (by exact_mod_cast he) hm horder
    (s2v_l1b_kval_cross_eigenseries_residue hζ he f g hf hg heigen)

end HodgeLean.Foundations.Program
