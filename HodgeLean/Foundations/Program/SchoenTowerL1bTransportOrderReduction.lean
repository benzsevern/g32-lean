import HodgeLean.Foundations.Program.SchoenTowerL1bKvalRamifiedFraction

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The local series data identify the weighted identity with an integer
congruence for the binomial coefficient's order. -/
theorem s2v_l1b_transport_order_iff
    {K : Type*} [Field K] {ζ : K} {e k : ℕ}
    (hζ : IsPrimitiveRoot ζ e) (he : e ≠ 0)
    (F G : PowerSeries K) (hF : F ≠ 0) (hG : G ≠ 0)
    (hcross : PowerSeries.rescale ζ F * G =
      PowerSeries.C (ζ ^ k) * (F * PowerSeries.rescale ζ G))
    {m q v w : ℤ} (hm : m = (e : ℤ) * q)
    (hram : m * ((F.order.toNat : ℤ) - (G.order.toNat : ℤ)) = (e : ℤ) * v) :
    (∃ l : ℤ, q * (k : ℤ) = w + m * l) ↔ Int.ModEq m v w := by
  have hv := s2v_l1b_kval_ramified_fraction_residue hζ he F G hF hG hcross hm hram
  constructor
  · rintro ⟨l, hl⟩
    apply hv.trans
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-l, ?_⟩
    rw [hl]
    ring
  · intro hw
    obtain ⟨l, hl⟩ := Int.modEq_iff_dvd.mp (hw.symm.trans hv)
    exact ⟨l, by linarith⟩

end HodgeLean.Foundations.Program
