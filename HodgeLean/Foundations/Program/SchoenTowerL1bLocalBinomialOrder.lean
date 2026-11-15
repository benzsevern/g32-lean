import HodgeLean.Foundations.Program.SchoenTowerL1bLocalFractionOrder

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A field binomial equation and compatible series presentations determine
the signed order of the generating fraction. -/
theorem s2v_l1b_local_binomial_order
    {R E K L : Type*} [CommRing R] [Field E] [Field K] [Field L]
    (ρ : R →+* E) (ψ : E →+* L) (ι : PowerSeries K →+* L)
    (hι : Function.Injective ι) (t : E) (a b : R)
    (F G A B : PowerSeries K)
    (hF : F ≠ 0) (hG : G ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (m : ℕ) (hpow : t ^ m = ρ a / ρ b)
    (ht : ψ t = ι F / ι G) (ha : ψ (ρ a) = ι A) (hb : ψ (ρ b) = ι B) :
    (m : ℤ) * ((F.order.toNat : ℤ) - (G.order.toNat : ℤ)) =
      (A.order.toNat : ℤ) - (B.order.toNat : ℤ) := by
  apply s2v_l1b_local_fraction_order F G A B hF hG hA hB m
  have h := congrArg ψ hpow
  rw [map_pow, map_div₀, ht, ha, hb, div_pow] at h
  have hιG : ι G ≠ 0 := fun h => hG (hι (h.trans ι.map_zero.symm))
  have hιB : ι B ≠ 0 := fun h => hB (hι (h.trans ι.map_zero.symm))
  apply hι
  simp only [map_mul, map_pow]
  exact (div_eq_div_iff (pow_ne_zero m hιG) hιB).mp h

end HodgeLean.Foundations.Program
