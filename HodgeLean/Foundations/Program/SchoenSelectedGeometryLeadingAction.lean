import HodgeLean.Foundations.Program.SchoenSelectedGeometryAnalyticFactor

noncomputable section
set_option maxHeartbeats 400000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- The leading term of an equivariant analytic germ relates the two tangent multipliers. -/
theorem s0_analytic_leading_equivariance
    {f g h : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hh : AnalyticAt ℂ h 0) (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hh0 : h 0 = 0)
    {n : ℕ} (hn : analyticOrderAt f 0 = n)
    (he : ∀ᶠ z in 𝓝 (0 : ℂ), f (g z) = h (f z)) :
    deriv h 0 = deriv g 0 ^ n := by
  obtain ⟨u, hu, hu0, hfu⟩ := hf.analyticOrderAt_eq_natCast.mp hn
  obtain ⟨v, hv, hv0, hgv⟩ := s0_analytic_first_factor hg hg0
  obtain ⟨w, hw, hw0, hhw⟩ := s0_analytic_first_factor hh hh0
  have hfg : ∀ᶠ z in 𝓝 (0 : ℂ), f (g z) = g z ^ n * u (g z) := by
    have h := hg.continuousAt.tendsto.eventually (by rw [hg0]; exact hfu)
    simpa only [sub_zero, smul_eq_mul] using h
  have hhf : ∀ᶠ z in 𝓝 (0 : ℂ), h (f z) = f z * w (f z) :=
    hf.continuousAt.tendsto.eventually (by rw [hf0]; exact hhw)
  let L := fun z : ℂ ↦ v z ^ n * u (g z)
  let R := fun z : ℂ ↦ u z * w (f z)
  have huG : ContinuousAt u (g 0) := by rw [hg0]; exact hu.continuousAt
  have hwF : ContinuousAt w (f 0) := by rw [hf0]; exact hw.continuousAt
  have hL : ContinuousAt L 0 :=
    (hv.continuousAt.pow n).mul (huG.comp hg.continuousAt)
  have hR : ContinuousAt R 0 :=
    hu.continuousAt.mul (hwF.comp hf.continuousAt)
  have hLR : L =ᶠ[𝓝[≠] (0 : ℂ)] R := by
    filter_upwards [nhdsWithin_le_nhds (he.and (hfu.and (hgv.and (hfg.and hhf)))),
      self_mem_nhdsWithin] with z ⟨he, hf, hg, hfg, hhf⟩ hz
    have hz0 : z ≠ 0 := hz
    apply mul_left_cancel₀ (pow_ne_zero n hz0)
    change z ^ n * (v z ^ n * u (g z)) = z ^ n * (u z * w (f z))
    rw [sub_zero, smul_eq_mul] at hf
    calc
      z ^ n * (v z ^ n * u (g z)) = (z * v z) ^ n * u (g z) := by rw [mul_pow]; ring
      _ = f (g z) := by rw [← hg]; exact hfg.symm
      _ = h (f z) := he
      _ = z ^ n * (u z * w (f z)) := by rw [hhf, hf]; ring
  have hlim : L 0 = R 0 :=
    tendsto_nhds_unique (hL.tendsto.mono_left nhdsWithin_le_nhds)
      ((hR.tendsto.mono_left nhdsWithin_le_nhds).congr' (hLR.mono fun _ h ↦ h.symm))
  simp only [L, R, hg0, hf0, hv0, hw0] at hlim
  exact (mul_right_cancel₀ hu0 (hlim.trans (mul_comm _ _))).symm

#print axioms s0_analytic_leading_equivariance
end HodgeLean.Foundations.Program
