import HodgeLean.Foundations.Program.SchoenCycleC1RamifiedPhase

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program

/-- The signed native rotation phase and actual ramification equation
identify the downstairs coefficient order modulo the covering degree. -/
theorem s2e_c1_ramified_rotation_residue
    (m e : ℕ) (hm : 0 < m) (he : 0 < e) (ε r n q : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hrel : (m : ℤ) * r = (e : ℤ) * n)
    (hphase : Complex.exp ((ε : ℂ) * (2 * Real.pi * Complex.I) / (e : ℂ)) ^ r =
      Complex.exp (2 * Real.pi * Complex.I / (m : ℂ)) ^ q) :
    (m : ℤ) ∣ n - ε * q := by
  let θ := Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))
  have hθ : IsPrimitiveRoot θ m := Complex.isPrimitiveRoot_exp m (Nat.ne_of_gt hm)
  have hne : θ ≠ 0 := Complex.exp_ne_zero _
  have heq : θ ^ (ε * n) = θ ^ q :=
    (s2e_c1_ramified_rotation_phase m e hm he ε r n hrel).symm.trans hphase
  have hz : θ ^ (ε * n - q) = 1 := by
    rw [zpow_sub₀ hne, heq, div_self (zpow_ne_zero _ hne)]
  have hd := (hθ.zpow_eq_one_iff_dvd (ε * n - q)).mp hz
  rcases hε with rfl | rfl
  · simpa only [one_mul] using hd
  · have h := dvd_neg.mpr hd
    simpa [add_comm] using h

end HodgeLean.Foundations.Program
