import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageTwo.Defs

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A literal integral parameter vanishes exactly with its base ratio when their positive powers differ by a selector unit in the original field. -/
theorem integral_unit_power_zero_evaluation
    {A L : Type} [CommRing A] [Field L] (F : A →+* L)
    (q t : normalizedChart F) (hq : IsUnit q) (s : A)
    (n : ℕ) (hn : 0 < n) (b : ℤ)
    (ht : (t : L) ^ n = (q : L) ^ b * F s)
    (ev : normalizedChart F →+* ℂ) :
    ev t = 0 ↔ ev (StageTwo.integralCoeff F s) = 0 := by
  obtain ⟨u, hu⟩ := hq
  have hc : ((↑(u ^ b) : normalizedChart F) : L) = (q : L) ^ b := by
    have hh := congrArg (fun z : Lˣ => (z : L))
      ((Units.map (normalizedChart F).subtype).map_zpow u b)
    simp only [Units.coe_map, Units.val_zpow_eq_zpow_val] at hh
    change ((↑(u ^ b) : normalizedChart F) : L) = ((↑u : normalizedChart F) : L) ^ b at hh
    rw [hu] at hh
    exact hh
  have heq : t ^ n = (↑(u ^ b) : normalizedChart F) * StageTwo.integralCoeff F s := by
    apply Subtype.ext
    change (t : L) ^ n = ((↑(u ^ b) : normalizedChart F) : L) * F s
    rw [hc]
    exact ht
  have hcoef : ev (↑(u ^ b) : normalizedChart F) ≠ 0 :=
    ((u ^ b).isUnit.map ev).ne_zero
  have hp := congrArg ev heq
  rw [map_pow, map_mul] at hp
  constructor
  · intro hz
    rw [hz, zero_pow (Nat.ne_of_gt hn)] at hp
    exact (mul_eq_zero.mp hp.symm).resolve_left hcoef
  · intro hz
    have ht0 : ev t ^ n = 0 := hp.trans (by rw [hz, mul_zero])
    exact (pow_eq_zero_iff (Nat.ne_of_gt hn)).mp ht0

end AlgebraicGeometry.RamifiedNormalization.StageFour
