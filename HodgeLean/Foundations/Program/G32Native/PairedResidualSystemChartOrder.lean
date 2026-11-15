import HodgeLean.Foundations.Program.G32Native.PairedResidualSystemAnalytic

/-! # Exact full-system divisor orders throughout a curve chart -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open HodgeLean.Adapters Filter Topology Manifold
open scoped ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- Corrected coefficients recover the adjusted divisor at every point of an isolated-pole chart. -/
theorem residual_normalized_pole_corrected_chart_order
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (y : Fin n → C)
    (hy : Function.Injective y) (w : b4c_MeroForm E C hE)
    (hw : (w : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0)
    (ha : ∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc hE w p) 0)
    (hzval : ∀ p ∈ Set.range y, ∀ u, w ⟨p, u⟩ = 0)
    (p : C) (z : ℂ)
    (ht : extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z ∈ (extChartAt 𝓘(ℂ, E) p).target)
    (haway : z ≠ 0 → (extChartAt 𝓘(ℂ, E) p).symm
      (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z) ∉ Set.range y)
    (g : ℂ → ℂ) (hg : AnalyticAt ℂ g z)
    (he : (fun ζ => (if p ∈ Set.range y then ζ else 1) * HurwitzPrymRR_loc hE w p ζ)
      =ᶠ[𝓝[≠] z] g) :
    ∃ d : ℕ, analyticOrderAt g z = d ∧ (d : ℤ) =
      (b4c_divForm (hE := hE) w + s2e_markedPoleDivisor y)
        ((extChartAt 𝓘(ℂ, E) p).symm
          (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z)) := by
  classical
  by_cases hz : z = 0
  · subst z
    simpa only [map_zero, add_zero, extChartAt_to_inv] using
      residual_normalized_pole_corrected_order hE y hy w hw ha hzval p g hg he
  let q := (extChartAt 𝓘(ℂ, E) p).symm
    (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z)
  have hq : q ∈ (extChartAt 𝓘(ℂ, E) p).source :=
    (extChartAt 𝓘(ℂ, E) p).map_target ht
  have hcoord : (b4cov_lineEquiv hE).symm
      (extChartAt 𝓘(ℂ, E) p q - extChartAt 𝓘(ℂ, E) p p) = z := by
    rw [(extChartAt 𝓘(ℂ, E) p).right_inv ht, add_sub_cancel_left,
      ContinuousLinearEquiv.symm_apply_apply]
  have hc := HurwitzPrymRR_ord_chart hE
    (w)
    w.property.1 p q hq
  rw [hcoord] at hc
  have hd := RiemannRochEichler_divForm_order hE w
    (residual_normalized_form_has_finite_order hE (Set.range y) w hw ha hzval) q
  have hord : meromorphicOrderAt g z =
      (((b4c_divForm (hE := hE) w + s2e_markedPoleDivisor y) q : ℤ) : WithTop ℤ) := by
    rw [← meromorphicOrderAt_congr he]
    have he' : meromorphicOrderAt (fun ζ => (if p ∈ Set.range y then ζ else 1) *
        HurwitzPrymRR_loc hE (w) p ζ) z =
        meromorphicOrderAt (HurwitzPrymRR_loc hE (w) p) z := by
      by_cases hp : p ∈ Set.range y
      · simp only [ite_eq_left hp]
        exact meromorphicOrderAt_mul_of_ne_zero analyticAt_id hz
      · simp only [ite_eq_right hp, one_mul]
    rw [he', ← hc, ← hd]
    simp only [Finsupp.add_apply,
      s2e_markedPoleDivisor_apply_outside y q (haway hz), add_zero]
  have hn : analyticOrderAt g z ≠ ⊤ := by
    intro ht'
    have hh := hg.meromorphicOrderAt_eq
    rw [ht', ENat.map_top, hord] at hh
    exact WithTop.coe_ne_top hh
  obtain ⟨d, hd'⟩ := ENat.ne_top_iff_exists.mp hn
  refine ⟨d, hd'.symm, ?_⟩
  rw [hg.meromorphicOrderAt_eq, ← hd', ENat.map_natCast] at hord
  exact_mod_cast hord

#print axioms residual_normalized_pole_corrected_chart_order
end HodgeLean.Foundations.Program.G32Native
