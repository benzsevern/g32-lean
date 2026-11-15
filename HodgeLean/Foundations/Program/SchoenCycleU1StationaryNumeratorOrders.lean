import HodgeLean.Foundations.Program.SchoenCycleU1AnalyticQuotientUnit
import HodgeLean.Foundations.Program.SchoenCycleU1StationaryNumerator

/-! # Differential variation divisibility detected by numerator orders -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- A stationary analytic numerator dominating the actual differential family
and having its exact base order forces analytic divisibility of the variation.
Source: Gunning--Rossi, Analytic Functions of Several Complex Variables,
Chapter II, section B, analytic division; ACGH, Geometry of Algebraic Curves I, Chapter I. -/
theorem s2e_u1_stationary_numerator_orders_divisibility
    (θ δ : ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (hθ : AnalyticAt ℂ θ 0) (hδ : AnalyticAt ℂ δ 0) (hF : AnalyticAt ℂ F (0, 0))
    (hord : ∀ᶠ tz in 𝓝 ((0, 0) : ℂ × ℂ),
      analyticOrderAt (fun z => θ z + tz.1 * δ z) tz.2 ≤
        analyticOrderAt (fun z => F (tz.1, z)) tz.2)
    (d : ℕ) (hFd : analyticOrderAt (fun z => F (0, z)) 0 = d)
    (hθd : analyticOrderAt θ 0 = d)
    (hstationary : ∀ᶠ z : ℂ in 𝓝 0, deriv (fun t => F (t, z)) 0 = 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ δ =ᶠ[𝓝 0] (fun z => g z * θ z) := by
  let P : ℂ × ℂ → ℂ := fun tz => θ tz.2 + tz.1 * δ tz.2
  have hPa : AnalyticAt ℂ P (0, 0) :=
    (hθ.comp_of_eq analyticAt_snd rfl).add
      (analyticAt_fst.mul (hδ.comp_of_eq analyticAt_snd rfl))
  let E : (Fin 1 → ℂ) × ℂ → ℂ × ℂ := fun tz => (tz.1 0, tz.2)
  have hEa : AnalyticAt ℂ E (0, 0) :=
    (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0).comp_of_eq
      analyticAt_fst rfl).prod analyticAt_snd
  let Fv := F ∘ E
  let Pv := P ∘ E
  have hdom : ∀ᶠ tz in 𝓝 ((0 : Fin 1 → ℂ), (0 : ℂ)),
      analyticOrderAt (fun z => Pv (tz.1, z)) tz.2 ≤
        analyticOrderAt (fun z => Fv (tz.1, z)) tz.2 :=
    hEa.continuousAt.tendsto.eventually hord
  have hFvd : analyticOrderAt (fun z => Fv (0, z)) 0 = d := hFd
  have hPvd : analyticOrderAt (fun z => Pv (0, z)) 0 = d := by
    simpa only [Pv, Function.comp_apply, E, P, Pi.zero_apply, zero_mul, add_zero] using hθd
  obtain ⟨u, hu, hu0, he⟩ := s2e_u1_analytic_unit_quotient_germ_of_orders Fv Pv
    (hF.comp_of_eq hEa rfl) (hPa.comp_of_eq hEa rfl) hdom d hFvd hPvd
  let S : ℂ × ℂ → (Fin 1 → ℂ) × ℂ := fun tz => ((fun _ => tz.1), tz.2)
  have hSa : AnalyticAt ℂ S (0, 0) := by
    apply AnalyticAt.prod _ analyticAt_snd
    apply AnalyticAt.pi
    intro i
    exact analyticAt_fst
  have he' : F =ᶠ[𝓝 ((0, 0) : ℂ × ℂ)] (fun tz => u (S tz) * P tz) :=
    he.comp_tendsto hSa.continuousAt.tendsto
  exact s2e_u1_stationary_numerator_factor_divisibility θ δ (u ∘ S) F
    (hu.comp_of_eq hSa rfl) hF hu0 he' hstationary

end HodgeLean.Foundations.Program
