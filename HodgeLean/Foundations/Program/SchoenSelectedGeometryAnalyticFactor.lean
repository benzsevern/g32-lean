import HodgeLean.Foundations.Program.HurwitzPrymCovNormalForm

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- An analytic function vanishing at zero has a first-order factor with the derivative as value. -/
theorem s0_analytic_first_factor {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 = deriv f 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), f z = z * u z := by
  have hord : (1 : ℕ∞) ≤ analyticOrderAt f 0 := by
    rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl,
      natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
    intro i hi
    rw [Nat.lt_one_iff.mp hi, iteratedDeriv_zero, hf0]
  obtain ⟨u, hu, hfu⟩ := (natCast_le_analyticOrderAt hf (n := 1)).mp hord
  have he : f =ᶠ[𝓝 0] fun z ↦ z * u z := by
    filter_upwards [hfu] with z hz
    simpa only [sub_zero, pow_one, smul_eq_mul] using hz
  refine ⟨u, hu, ?_, he⟩
  have hd : HasDerivAt (fun z ↦ z * u z) (u 0) 0 := by
    have hd := (hasDerivAt_id' (0 : ℂ)).mul hu.differentiableAt.hasDerivAt
    simp only [one_mul, zero_mul, add_zero] at hd
    exact hd
  rw [he.deriv_eq, hd.deriv]

#print axioms s0_analytic_first_factor
end HodgeLean.Foundations.Program
