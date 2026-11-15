import HodgeLean.Foundations.Program.SchoenCycleU1PartialDerivative

/-! # First variation of a local preparation identity -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- A stationary prepared factor makes the first variation locally divisible
by the original coefficient through an analytic quotient.
Source: ACGH, Geometry of Algebraic Curves I, Chapters I and IV;
Mathlib, the derivative product rule and analytic parameter derivatives. -/
theorem s2e_u1_stationary_preparation_analytic_quotient
    (θ δ : ℂ → ℂ) (u q : ℂ × ℂ → ℂ)
    (hu : AnalyticAt ℂ u (0, 0)) (hq : AnalyticAt ℂ q (0, 0))
    (hu0 : u (0, 0) ≠ 0)
    (he : (fun tz : ℂ × ℂ => θ tz.2 + tz.1 * δ tz.2) =ᶠ[𝓝 (0, 0)]
      (fun tz => u tz * q tz))
    (hstationary : ∀ᶠ z : ℂ in 𝓝 0, deriv (fun t => q (t, z)) 0 = 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ δ =ᶠ[𝓝 0] (fun z => g z * θ z) := by
  let g := fun z : ℂ => deriv (fun t => u (t, z)) 0 / u (0, z)
  have huZ : AnalyticAt ℂ (fun z : ℂ => u (0, z)) 0 :=
    hu.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  refine ⟨g, (s2e_u1_analyticAt_parameter_derivative u hu).div huZ hu0, ?_⟩
  have hc : ∀ᶠ z : ℂ in 𝓝 0,
      (fun t => θ z + t * δ z) =ᶠ[𝓝 0] (fun t => u (t, z) * q (t, z)) := by
    have ht : Tendsto (fun tz : ℂ × ℂ => (tz.2, tz.1))
        (𝓝 ((0, 0) : ℂ × ℂ)) (𝓝 ((0, 0) : ℂ × ℂ)) :=
      (continuousAt_snd.prodMk continuousAt_fst).tendsto
    have hs := he.comp_tendsto ht
    rw [nhds_prod_eq] at hs
    exact Filter.Eventually.curry hs
  have ht : Tendsto (fun z : ℂ => (0, z)) (𝓝 0) (𝓝 ((0, 0) : ℂ × ℂ)) :=
    (continuousAt_const.prodMk continuousAt_id).tendsto
  have hua : ∀ᶠ z : ℂ in 𝓝 0, AnalyticAt ℂ u (0, z) :=
    ht.eventually hu.eventually_analyticAt
  have hqa : ∀ᶠ z : ℂ in 𝓝 0, AnalyticAt ℂ q (0, z) :=
    ht.eventually hq.eventually_analyticAt
  filter_upwards [hc, hua, hqa, hstationary, huZ.continuousAt.eventually_ne hu0]
    with z hz huz hqz hsz hnz
  have huT : AnalyticAt ℂ (fun t : ℂ => u (t, z)) 0 :=
    huz.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
  have hqT : AnalyticAt ℂ (fun t : ℂ => q (t, z)) 0 :=
    hqz.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
  have hbase : θ z = u (0, z) * q (0, z) := by simpa using hz.self_of_nhds
  have hδ : δ z = deriv (fun t => u (t, z)) 0 * q (0, z) := by
    have hd := hz.deriv_eq
    simpa only [deriv_const_add, deriv_mul_const_field, deriv_id'', one_mul,
      deriv_fun_mul huT.differentiableAt hqT.differentiableAt, hsz, mul_zero, add_zero] using hd
  change δ z = (deriv (fun t => u (t, z)) 0 / u (0, z)) * θ z
  rw [hδ, hbase]
  field_simp [hnz] <;> ring

end HodgeLean.Foundations.Program
