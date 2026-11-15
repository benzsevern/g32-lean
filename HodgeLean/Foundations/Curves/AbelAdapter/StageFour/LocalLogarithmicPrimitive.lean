import HodgeLean.Foundations.Program.RiemannRoch
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.Deriv.ZPow

noncomputable section
open Filter Topology Metric
open TauCeti.Contour
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Source: Forster, Lectures on Riemann Surfaces, §10, exponentials of local primitives. -/
theorem analytic_unit_with_logarithmicDerivative {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ (∀ z, u z ≠ 0) ∧
      ∀ᶠ z in 𝓝 0, HasDerivAt u (g z * u z) z := by
  obtain ⟨r, hr, hrg⟩ := Metric.eventually_nhds_iff.mp hg.eventually_analyticAt
  have hd : DifferentiableOn ℂ g (ball 0 r) := fun z hz =>
    (hrg (by simpa only [mem_ball, dist_comm] using hz)).differentiableAt.differentiableWithinAt
  obtain ⟨G, hG⟩ := hd.isExactOn_ball
  have hGa : AnalyticAt ℂ G 0 :=
    (show DifferentiableOn ℂ G (ball 0 r) from fun z hz =>
      (hG z hz).differentiableAt.differentiableWithinAt).analyticAt (ball_mem_nhds 0 hr)
  refine ⟨fun z => Complex.exp (G z), hGa.cexp, fun z => Complex.exp_ne_zero _, ?_⟩
  filter_upwards [ball_mem_nhds (0 : ℂ) hr] with z hz
  simpa only [mul_comm] using (hG z hz).cexp

/-- Source: Forster, Lectures on Riemann Surfaces, §§10, 18, local integration at integral residues. -/
theorem meromorphic_logarithmicPrimitive_at_integral_residue {f : ℂ → ℂ}
    (hf : MeromorphicAt f 0) (ho : (-1 : WithTop ℤ) ≤ meromorphicOrderAt f 0)
    (n : ℤ) (hr : residue f 0 = (n : ℂ)) :
    ∃ F : ℂ → ℂ, MeromorphicAt F 0 ∧ meromorphicOrderAt F 0 = (n : WithTop ℤ) ∧
      ∀ᶠ z in 𝓝[≠] 0, F z ≠ 0 ∧ HasDerivAt F (f z * F z) z := by
  obtain ⟨g, hg, he⟩ := RiemannRochEichler_simple_pole_split hf ho
  obtain ⟨u, hu, hune, hud⟩ := analytic_unit_with_logarithmicDerivative hg
  have hm : MeromorphicAt (fun z : ℂ => z ^ n) 0 := analyticAt_id.meromorphicAt.zpow n
  refine ⟨fun z => u z * z ^ n, hu.meromorphicAt.mul hm, ?_, ?_⟩
  · change meromorphicOrderAt (u * (id ^ n)) 0 = n
    rw [meromorphicOrderAt_mul_of_ne_zero hu (hune 0),
      meromorphicOrderAt_zpow analyticAt_id.meromorphicAt, meromorphicOrderAt_id, mul_one]
  · filter_upwards [he, hud.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hudz hzne
    have hz0 : z ≠ 0 := hzne
    refine ⟨mul_ne_zero (hune z) (zpow_ne_zero n hz0), ?_⟩
    convert hudz.mul (hasDerivAt_zpow n z (Or.inl hz0)) using 1
    rw [hz, hr, sub_zero, zpow_sub₀ hz0 n 1, zpow_one]
    field_simp
    <;> ring

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
