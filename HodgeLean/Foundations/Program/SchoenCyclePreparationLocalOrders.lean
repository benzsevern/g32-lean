import HodgeLean.Foundations.Program.SchoenCyclePairedLocalPolynomial

/-! # Uniform orders in a supplied preparation -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic4
namespace HodgeLean.Foundations.Program

/-- A supplied preparation retains all vertical orders on one fixed nearby disc.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14. -/
theorem s2e_preparation_uniform_vertical_orders
    {n d : ℕ} (f u : (Fin n → ℂ) × ℂ → ℂ)
    (c : Fin d → (Fin n → ℂ) → ℂ)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hprep : f =ᶠ[𝓝 0] fun tz => u tz * monicInLast c tz) :
    ∃ r > 0, ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), ∀ z ∈ Metric.ball (0 : ℂ) r,
      AnalyticAt ℂ (fun w => f (t, w)) z ∧
      analyticOrderAt (fun w => f (t, w)) z =
        analyticOrderAt (fun w => monicInLast c (t, w)) z := by
  have hgood : ∀ᶠ tz in 𝓝 (0 : (Fin n → ℂ) × ℂ),
      f tz = u tz * monicInLast c tz ∧ AnalyticAt ℂ u tz ∧ u tz ≠ 0 := by
    filter_upwards [hprep, hu.eventually_analyticAt, hu.continuousAt.eventually_ne hu0]
      with tz hp ha hn
    exact ⟨hp, ha, hn⟩
  obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp hgood
  obtain ⟨r, hr, hWr⟩ := Metric.mem_nhds_iff.mp hW
  refine ⟨r, hr, ?_⟩
  filter_upwards [hV] with t ht
  intro z hz
  have htz := hVW (show (t, z) ∈ V ×ˢ W from ⟨ht, hWr hz⟩)
  have hu' : AnalyticAt ℂ (fun w => u (t, w)) z :=
    htz.2.1.comp (f := fun w : ℂ => (t, w)) (analyticAt_const.prod analyticAt_id)
  have hP : AnalyticAt ℂ (fun w => monicInLast c (t, w)) z := by
    change AnalyticAt ℂ (fun w : ℂ => w ^ d + ∑ j : Fin d, c j t * w ^ (j : ℕ)) z
    apply AnalyticAt.add (analyticAt_id.pow d)
    apply Finset.analyticAt_fun_sum
    intro j _
    exact analyticAt_const.mul (analyticAt_id.pow j.val)
  have he : (fun w => f (t, w)) =ᶠ[𝓝 z] fun w => u (t, w) * monicInLast c (t, w) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    exact (hVW (show (t, w) ∈ V ×ˢ W from ⟨ht, hWr hw⟩)).1
  refine ⟨(hu'.mul hP).congr he.symm, ?_⟩
  rw [analyticOrderAt_congr he]
  change analyticOrderAt ((fun w => u (t, w)) * (fun w => monicInLast c (t, w))) z = _
  rw [analyticOrderAt_mul hu' hP, hu'.analyticOrderAt_eq_zero.mpr htz.2.2, zero_add]

#print axioms s2e_preparation_uniform_vertical_orders
end HodgeLean.Foundations.Program
