import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageTwo.Defs

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The same original-field selector and the inverse first-chart parameter are integral on the reciprocal binomial chart. -/
theorem reciprocal_binomial_integral_parameters
    {B L : Type} [CommRing B] [Field L] (G : B →+* L)
    (g n : ℕ) (hg : 0 < g) (hn : 0 < n)
    (ε : Bˣ) (s : B) (q t : L) (b : ℤ)
    (hq : q ^ g = G ε) (ht : t ^ n = q ^ b * (G s)⁻¹) :
    ∃ qB tB : normalizedChart G,
      (qB : L) = q ∧ (tB : L) = t⁻¹ ∧
      qB ^ g = StageTwo.integralCoeff G ε ∧
      (tB : L) ^ n = (qB : L) ^ (-b) * G s := by
  letI := G.toAlgebra
  have hqint : _root_.IsIntegral B q := by
    apply IsIntegral.of_pow hg
    rw [hq]
    exact isIntegral_algebraMap
  have hqinv : _root_.IsIntegral B q⁻¹ := by
    apply IsIntegral.of_pow hg
    rw [inv_pow, hq, ← map_units_inv G ε]
    exact isIntegral_algebraMap
  have hqz (c : ℤ) : _root_.IsIntegral B (q ^ c) := by
    cases c with
    | ofNat k =>
      change _root_.IsIntegral B (q ^ (k : ℤ))
      rw [zpow_natCast]
      exact hqint.pow k
    | negSucc k => simpa only [zpow_negSucc, inv_pow] using hqinv.pow (k + 1)
  have hti : (t⁻¹) ^ n = q ^ (-b) * G s := by
    rw [inv_pow, ht, mul_inv_rev, inv_inv, ← zpow_neg]
    exact mul_comm _ _
  have htint : _root_.IsIntegral B t⁻¹ := by
    apply IsIntegral.of_pow hn
    rw [hti]
    exact (hqz (-b)).mul (isIntegral_algebraMap (x := s))
  let qB : normalizedChart G := ⟨q, hqint⟩
  let tB : normalizedChart G := ⟨t⁻¹, htint⟩
  refine ⟨qB, tB, rfl, rfl, ?_, hti⟩
  apply Subtype.ext
  exact hq

end AlgebraicGeometry.RamifiedNormalization.StageFour
