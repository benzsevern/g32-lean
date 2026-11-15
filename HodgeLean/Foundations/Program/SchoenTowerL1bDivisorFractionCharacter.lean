import HodgeLean.Foundations.Program.SchoenTowerL1bTransportPowerCharacter
import Mathlib.RingTheory.Localization.FractionRing

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A rational eigenfunction for a power rescaling has the weighted global-character residue. -/
theorem s2v_l1b_divisor_fraction_power_character
    {R E K : Type*} [CommRing R] [IsDomain R] [Field E] [Field K]
    [Algebra R E] [IsFractionRing R E]
    (ι : R →+* PowerSeries K) (hι : Function.Injective ι)
    (θ : R →+* R) (τ : E →+* E) (ζ : K)
    (hτ : ∀ a : R, τ (algebraMap R E a) = algebraMap R E (θ a))
    {q : ℕ}
    (hθ : ∀ a : R, ι (θ a) = PowerSeries.rescale (ζ ^ q) (ι a))
    {e k : ℕ} (he : e ≠ 0) (hζ : IsPrimitiveRoot ζ e)
    (c : R) (hc : ι c = PowerSeries.C (ζ ^ k))
    (t : E) (ht : t ≠ 0) (heigen : τ t = algebraMap R E c * t) :
    ∃ a b : R, a ≠ 0 ∧ b ≠ 0 ∧
      t = algebraMap R E a / algebraMap R E b ∧
      Int.ModEq (e : ℤ)
        ((q : ℤ) * (((ι a).order.toNat : ℤ) - ((ι b).order.toNat : ℤ))) (k : ℤ) := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R t
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    intro ha
    rw [ha, map_zero, zero_div] at hab
    exact ht hab.symm
  have hbE : algebraMap R E b ≠ 0 := by simpa only [map_zero] using (IsFractionRing.injective R E).ne hb0
  have hθb : algebraMap R E (θ b) ≠ 0 := by
    rw [← hτ]
    simpa only [map_zero] using τ.injective.ne hbE
  have hrat : algebraMap R E (θ a) / algebraMap R E (θ b) =
      (algebraMap R E c * algebraMap R E a) / algebraMap R E b := by
    rw [← hτ, ← hτ, ← map_div₀, hab, heigen, ← hab, mul_div_assoc]
  have hcrossR : θ a * b = c * (a * θ b) := by
    apply IsFractionRing.injective R E
    simpa only [map_mul, mul_assoc] using (div_eq_div_iff hθb hbE).mp hrat
  have hcross : PowerSeries.rescale (ζ ^ q) (ι a) * ι b =
      PowerSeries.C (ζ ^ k) * (ι a * PowerSeries.rescale (ζ ^ q) (ι b)) := by
    have h := congrArg ι hcrossR
    simpa only [map_mul, hθ, hc] using h
  refine ⟨a, b, ha0, hb0, hab.symm, ?_⟩
  exact s2v_l1b_transport_cross_power_character_residue hζ he (ι a) (ι b)
    (by simpa only [map_zero] using hι.ne ha0)
    (by simpa only [map_zero] using hι.ne hb0) hcross

end HodgeLean.Foundations.Program
