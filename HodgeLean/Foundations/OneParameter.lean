import HodgeLean.Foundations.ChartGroupLaw
import HodgeLean.Foundations.LocalOneParameter
import Mathlib.Analysis.ODE.ExistUnique

/-!
# One-parameter curves in the identity chart

Stage S11. HC no distance; AV milestone no distance. This retires nothing.
The coordinate space is `Fin d → ℂ`, regarded as a real normed space for real time.
This keeps S10's coordinates and supplies the real tangent directions needed by S12.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj NNReal
open Filter Topology Set Metric

namespace HodgeLean.Foundations
noncomputable section

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
  [SmoothOfRelativeDimension d X.hom]

/-- The coordinate vector field `D₂F(u,0)v`.

Source: constructed here for the identity-chart ODE; Mumford, Abelian Varieties, §1. -/
def chartVectorField (v u : Fin d → ℂ) : Fin d → ℂ :=
  fderiv ℂ (chartGroupLaw X d) (u, 0) (0, v)

example (v u : Fin d → ℂ) : chartVectorField X d v u =
    fderiv ℂ (chartGroupLaw X d) (u, 0) (0, v) := rfl

/-- The coordinate vector field takes its prescribed value at the identity.

Source: constructed here from S10's differential of multiplication. -/
theorem chartVectorField_origin (v : Fin d → ℂ) : chartVectorField X d v 0 = v := by
  simp [chartVectorField, fderiv_chartGroupLaw]

example (v : Fin d → ℂ) : chartVectorField X d v 0 = v :=
  chartVectorField_origin X d v

/-- The vector field is continuously differentiable over the reals near the origin.

Source: constructed here from S10's analyticity and Mathlib's analytic differentiation. -/
theorem contDiffAt_chartVectorField (v : Fin d → ℂ) :
    ContDiffAt ℝ 1 (chartVectorField X d v) 0 := by
  have hp : ContDiffAt ℂ 1 (fun u : Fin d → ℂ ↦ (u, (0 : Fin d → ℂ))) 0 :=
    contDiffAt_id.prodMk contDiffAt_const
  have hD : ContDiffAt ℂ 1
      (fun u : Fin d → ℂ ↦ fderiv ℂ (chartGroupLaw X d) (u, 0)) 0 :=
    ((analyticAt_chartGroupLaw X d).fderiv.contDiffAt).comp
      (f := fun u : Fin d → ℂ ↦ (u, (0 : Fin d → ℂ))) 0 hp
  have h : ContDiffAt ℂ 1 (chartVectorField X d v) 0 :=
    hD.clm_apply (contDiffAt_const (c := ((0 : Fin d → ℂ), v)))
  exact h.restrict_scalars ℝ

example (v : Fin d → ℂ) : ContDiffAt ℝ 1 (chartVectorField X d v) 0 :=
  contDiffAt_chartVectorField X d v

/-- Uniform spatial Lipschitz and norm bounds on a ball give a positive time interval
for Picard–Lindelöf, also for initial points in a smaller ball.

Source: Mathlib `IsPicardLindelof.of_contDiffAt_one`, applied to the analytic chart law. -/
theorem chartVectorField_picardLindelof (v : Fin d → ℂ) :
    ∃ (ε : ℝ) (hε : 0 < ε) (a r L K : ℝ≥0), 0 < r ∧
      ∀ t₀ : ℝ, IsPicardLindelof (fun _ ↦ chartVectorField X d v)
        (tmin := t₀ - ε) (tmax := t₀ + ε)
        ⟨t₀, by simp [le_of_lt hε]⟩ 0 a r L K := by
  obtain ⟨ε, hε, a, r, L, K, hr, h⟩ :=
    IsPicardLindelof.of_contDiffAt_one (contDiffAt_chartVectorField X d v)
  exact ⟨ε, hε, a, r, L, K, hr, h⟩

example (v : Fin d → ℂ) :
    ∃ (ε : ℝ) (hε : 0 < ε) (a r L K : ℝ≥0), 0 < r ∧
      ∀ t₀ : ℝ, IsPicardLindelof (fun _ ↦ chartVectorField X d v)
        (tmin := t₀ - ε) (tmax := t₀ + ε)
        ⟨t₀, by simp [le_of_lt hε]⟩ 0 a r L K := chartVectorField_picardLindelof X d v

/-- A local solution through the origin with its prescribed initial velocity.

Source: Mathlib Picard–Lindelöf (`ContDiffAt` local integral-curve existence). -/
theorem exists_chartIntegralCurve (v : Fin d → ℂ) :
    ∃ u : ℝ → (Fin d → ℂ), u 0 = 0 ∧ HasDerivAt u v 0 ∧
      ∃ ε > (0 : ℝ), ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt u (chartVectorField X d v (u t)) t := by
  obtain ⟨u, hu, ε, hε, h⟩ :=
    (contDiffAt_chartVectorField X d v).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  have h0 := h 0 (show 0 ∈ Ioo (0 - ε) (0 + ε) by constructor <;> linarith)
  refine ⟨u, hu, ?_, ε, hε, ?_⟩
  · simpa [hu, chartVectorField_origin] using h0
  · simpa using h

example (v : Fin d → ℂ) : ∃ u : ℝ → (Fin d → ℂ), u 0 = 0 ∧ HasDerivAt u v 0 := by
  obtain ⟨u, hu, hv, _⟩ := exists_chartIntegralCurve X d v
  exact ⟨u, hu, hv⟩

/-- Two local integral curves with initial value zero agree near time zero.

Source: Mathlib `ODE_solution_unique_of_eventually`, using the local Lipschitz bound. -/
theorem chartIntegralCurve_unique (v : Fin d → ℂ) {u w : ℝ → (Fin d → ℂ)}
    (hu : u 0 = 0) (hw : w 0 = 0)
    (hdu : ∀ᶠ t in 𝓝 0, HasDerivAt u (chartVectorField X d v (u t)) t)
    (hdw : ∀ᶠ t in 𝓝 0, HasDerivAt w (chartVectorField X d v (w t)) t) :
    u =ᶠ[𝓝 0] w := by
  obtain ⟨K, s, hs, hK⟩ := (contDiffAt_chartVectorField X d v).exists_lipschitzOnWith
  have hcu : ContinuousAt u 0 := (hdu.self_of_nhds).continuousAt
  have hcw : ContinuousAt w 0 := (hdw.self_of_nhds).continuousAt
  have hus : ∀ᶠ t in 𝓝 0, u t ∈ s := hcu (hu ▸ hs)
  have hws : ∀ᶠ t in 𝓝 0, w t ∈ s := hcw (hw ▸ hs)
  exact ODE_solution_unique_of_eventually (v := fun _ ↦ chartVectorField X d v)
    (s := fun _ ↦ s) (Filter.Eventually.of_forall fun _ ↦ hK)
    (hdu.and hus) (hdw.and hws) (hu.trans hw.symm)

example (v : Fin d → ℂ) {u w : ℝ → (Fin d → ℂ)}
    (hu : u 0 = 0) (hw : w 0 = 0)
    (hdu : ∀ᶠ t in 𝓝 0, HasDerivAt u (chartVectorField X d v (u t)) t)
    (hdw : ∀ᶠ t in 𝓝 0, HasDerivAt w (chartVectorField X d v (w t)) t) :
    u =ᶠ[𝓝 0] w := chartIntegralCurve_unique X d v hu hw hdu hdw

/-- An integral curve of the chart vector field through zero is `C¹` near zero.

Source: constructed here from continuity of the analytic vector field and the ODE. -/
theorem contDiffAt_chartIntegralCurve (v : Fin d → ℂ) {u : ℝ → (Fin d → ℂ)}
    (hu : u 0 = 0)
    (hdu : ∀ᶠ t in 𝓝 0, HasDerivAt u (chartVectorField X d v (u t)) t) :
    ContDiffAt ℝ 1 u 0 := by
  have hcu := hdu.self_of_nhds.continuousAt
  have hv : ∀ᶠ t in 𝓝 0, ContinuousAt (chartVectorField X d v) (u t) := by
    have h := ((contDiffAt_chartVectorField X d v).eventually (by simp)).mono
      (fun _ h ↦ h.continuousAt)
    exact hcu (hu ▸ h)
  obtain ⟨s, hs, hsopen, hs0⟩ := _root_.mem_nhds_iff.mp (hdu.and hv)
  apply contDiffAt_one_iff.mpr
  refine ⟨fun t ↦ ContinuousLinearMap.toSpanSingleton ℝ (chartVectorField X d v (u t)),
    s, hsopen.mem_nhds hs0, ?_, fun t ht ↦ (hs ht).1.hasFDerivAt⟩
  intro t ht
  have hc := (hs ht).2.comp (hs ht).1.continuousAt
  exact (ContinuousLinearMap.toSpanSingletonCLE.continuous.continuousAt.comp hc).continuousWithinAt

example (v : Fin d → ℂ) {u : ℝ → (Fin d → ℂ)} (hu : u 0 = 0)
    (hdu : ∀ᶠ t in 𝓝 0, HasDerivAt u (chartVectorField X d v (u t)) t) :
    ContDiffAt ℝ 1 u 0 := contDiffAt_chartIntegralCurve X d v hu hdu

/-- A chosen local solution of `u' = D₂F(u,0)v` through zero.
Only its germ at zero is specified; values outside the existence interval are arbitrary.

Source: constructed here by Picard–Lindelöf in S10's normalized identity chart. -/
def chartIntegralCurve (v : Fin d → ℂ) : ℝ → (Fin d → ℂ) :=
  (exists_chartIntegralCurve X d v).choose

/-- The chosen solution starts at zero.

Source: constructed here from Picard–Lindelöf's initial condition. -/
theorem chartIntegralCurve_zero (v : Fin d → ℂ) : chartIntegralCurve X d v 0 = 0 :=
  (exists_chartIntegralCurve X d v).choose_spec.1

example (v : Fin d → ℂ) : chartIntegralCurve X d v 0 = 0 := chartIntegralCurve_zero X d v

/-- The chosen solution satisfies its ODE on a neighborhood of time zero.

Source: constructed here from Picard–Lindelöf's differential equation. -/
theorem chartIntegralCurve_ode (v : Fin d → ℂ) :
    ∀ᶠ t in 𝓝 0, HasDerivAt (chartIntegralCurve X d v)
      (chartVectorField X d v (chartIntegralCurve X d v t)) t := by
  obtain ⟨ε, hε, h⟩ := (exists_chartIntegralCurve X d v).choose_spec.2.2
  exact Filter.eventually_of_mem (Ioo_mem_nhds (by linarith) hε) h

example (v : Fin d → ℂ) :
    ∀ᶠ t in 𝓝 0, HasDerivAt (chartIntegralCurve X d v)
      (chartVectorField X d v (chartIntegralCurve X d v t)) t := chartIntegralCurve_ode X d v

/-- The initial velocity of the chosen solution is the prescribed tangent vector.

Source: constructed here from Picard–Lindelöf and `D₂F(0,0) = id`. -/
theorem hasDerivAt_chartIntegralCurve (v : Fin d → ℂ) :
    HasDerivAt (chartIntegralCurve X d v) v 0 :=
  (exists_chartIntegralCurve X d v).choose_spec.2.1

example (v : Fin d → ℂ) : HasDerivAt (chartIntegralCurve X d v) v 0 :=
  hasDerivAt_chartIntegralCurve X d v

/-- The chosen integral curve is continuously differentiable near zero.

Source: constructed here from the ODE and the analytic vector field. -/
theorem chartIntegralCurve_contDiffAt (v : Fin d → ℂ) :
    ContDiffAt ℝ 1 (chartIntegralCurve X d v) 0 :=
  contDiffAt_chartIntegralCurve X d v (chartIntegralCurve_zero X d v)
    (chartIntegralCurve_ode X d v)

example (v : Fin d → ℂ) : ContDiffAt ℝ 1 (chartIntegralCurve X d v) 0 :=
  chartIntegralCurve_contDiffAt X d v

private theorem chart_one_source : (1 : ComplexPoint X) ∈ (identityChart X d).source :=
  mem_localChart_source X d 1

private theorem chart_zero_target : (0 : Fin d → ℂ) ∈ (identityChart X d).target := by
  rw [← identityChart_one X d]
  exact (identityChart X d).map_source (chart_one_source X d)

private theorem chart_symm_zero : (identityChart X d).symm 0 = 1 := by
  rw [← identityChart_one X d]
  exact (identityChart X d).left_inv (chart_one_source X d)

private theorem chart_symm_continuousAt : ContinuousAt (identityChart X d).symm 0 :=
  (identityChart X d).symm.continuousAt (chart_zero_target X d)

private theorem chart_product_source :
    ∀ᶠ p : (Fin d → ℂ) × (Fin d → ℂ) in 𝓝 (0, 0),
      (identityChart X d).symm p.1 * (identityChart X d).symm p.2 ∈
        (identityChart X d).source := by
  have h : ContinuousAt (fun p : (Fin d → ℂ) × (Fin d → ℂ) ↦
      (identityChart X d).symm p.1 * (identityChart X d).symm p.2) (0, 0) :=
    ((chart_symm_continuousAt X d).comp (f := Prod.fst) continuousAt_fst).mul
      ((chart_symm_continuousAt X d).comp (f := Prod.snd) continuousAt_snd)
  have h0 : (identityChart X d).symm 0 * (identityChart X d).symm 0 = 1 := by
    simp [chart_symm_zero]
  apply h.tendsto.eventually
  change (identityChart X d).source ∈
    𝓝 ((identityChart X d).symm 0 * (identityChart X d).symm 0)
  rw [h0]
  exact (identityChart X d).open_source.mem_nhds (chart_one_source X d)

private theorem chart_assoc_eventually :
    ∀ᶠ p : ((Fin d → ℂ) × (Fin d → ℂ)) × (Fin d → ℂ) in 𝓝 ((0, 0), 0),
      chartGroupLaw X d (chartGroupLaw X d p.1, p.2) =
        chartGroupLaw X d (p.1.1, chartGroupLaw X d (p.1.2, p.2)) := by
  have hab := (continuousAt_fst (p := (((0, 0) : (Fin d → ℂ) × (Fin d → ℂ)),
    (0 : Fin d → ℂ)))).tendsto.eventually (chart_product_source X d)
  have hbc := (continuousAt_fst.snd.prodMk continuousAt_snd
    (x := (((0, 0) : (Fin d → ℂ) × (Fin d → ℂ)), (0 : Fin d → ℂ)))).tendsto.eventually (chart_product_source X d)
  filter_upwards [hab, hbc] with p hab hbc
  simp only [chartGroupLaw, (identityChart X d).left_inv hab,
    (identityChart X d).left_inv hbc, mul_assoc]

private theorem chart_covariance (v : Fin d → ℂ) :
    ∀ᶠ p : (Fin d → ℂ) × (Fin d → ℂ) in 𝓝 (0, 0),
      fderiv ℂ (chartGroupLaw X d) p (0, chartVectorField X d v p.2) =
        chartVectorField X d v (chartGroupLaw X d p) := by
  let F := chartGroupLaw X d
  have hF0 : F (0, 0) = 0 := by
    simpa using chartGroupLaw_zero_right X d (chart_zero_target X d)
  have hF := (analyticAt_chartGroupLaw X d).eventually_analyticAt
  have hFprod : ContinuousAt (fun p ↦ (F p, (0 : Fin d → ℂ))) (0, 0) :=
    (analyticAt_chartGroupLaw X d).continuousAt.prodMk continuousAt_const
  have houter : ∀ᶠ p in 𝓝 (0, 0), AnalyticAt ℂ F (F p, 0) :=
    hFprod.tendsto.eventually (by
      change ∀ᶠ p in 𝓝 (F (0, 0), (0 : Fin d → ℂ)), AnalyticAt ℂ F p
      rw [hF0]
      exact hF)
  have hinner : ∀ᶠ p : (Fin d → ℂ) × (Fin d → ℂ) in 𝓝 (0, 0),
      AnalyticAt ℂ F (p.2, 0) :=
    (continuousAt_snd.prodMk continuousAt_const
      (x := ((0 : Fin d → ℂ), (0 : Fin d → ℂ)))).tendsto.eventually hF
  have hassoc : ∀ᶠ p : (Fin d → ℂ) × (Fin d → ℂ) in 𝓝 (0, 0),
      ∀ᶠ w in 𝓝 0, F (F p, w) = F (p.1, F (p.2, w)) := by
    have h := chart_assoc_eventually X d
    rw [nhds_prod_eq] at h
    exact h.curry
  have ht : ∀ᶠ p : (Fin d → ℂ) × (Fin d → ℂ) in 𝓝 (0, 0),
      p.2 ∈ (identityChart X d).target :=
    continuousAt_snd ((identityChart X d).open_target.mem_nhds (chart_zero_target X d))
  filter_upwards [hF, houter, hinner, hassoc, ht] with p hp ho hi ha ht
  have hz : F (p.2, 0) = p.2 := chartGroupLaw_zero_right X d ht
  have hright := hi.differentiableAt.hasFDerivAt.comp 0
    (hasFDerivAt_prodMk_right (𝕜 := ℂ) p.2 (0 : Fin d → ℂ))
  have hleft := ho.differentiableAt.hasFDerivAt.comp 0
    (hasFDerivAt_prodMk_right (𝕜 := ℂ) (F p) (0 : Fin d → ℂ))
  have hp' : HasFDerivAt F (fderiv ℂ F p) (p.1, F (p.2, 0)) := by
    simpa only [hz] using hp.differentiableAt.hasFDerivAt
  have hr := hp'.comp 0 ((hasFDerivAt_const p.1 0).prodMk hright)
  have he := hleft.unique (hr.congr_of_eventuallyEq ha)
  exact (DFunLike.congr_fun he v).symm

/-- The local integral curve respects the coordinate group law for sufficiently small times.
The same interval works for both time variables.

Source: constructed here by differentiating local associativity and applying ODE uniqueness. -/
theorem chartIntegralCurve_local_add (v : Fin d → ℂ) :
    ∃ δ > (0 : ℝ), ∀ s t : ℝ, |s| < δ → |t| < δ →
      chartGroupLaw X d (chartIntegralCurve X d v s, chartIntegralCurve X d v t) =
        chartIntegralCurve X d v (s + t) := by
  let u := chartIntegralCurve X d v
  let V := chartVectorField X d v
  let F := chartGroupLaw X d
  have hu0 : u 0 = 0 := chartIntegralCurve_zero X d v
  have hF0 : F (0, 0) = 0 := chartGroupLaw_zero_right X d (chart_zero_target X d)
  have huc : ContinuousAt u 0 := (hasDerivAt_chartIntegralCurve X d v).continuousAt
  have huc' : ContinuousAt u (0 + 0) := by simpa using huc
  have hp : ContinuousAt (fun p : ℝ × ℝ ↦ (u p.1, u p.2)) (0, 0) :=
    (huc.comp (f := Prod.fst) continuousAt_fst).prodMk
      (huc.comp (f := Prod.snd) continuousAt_snd)
  have hsum : ContinuousAt (fun p : ℝ × ℝ ↦ u (p.1 + p.2)) (0, 0) :=
    huc'.comp (f := fun p : ℝ × ℝ ↦ p.1 + p.2) (continuousAt_fst.add continuousAt_snd)
  have hFc : ContinuousAt F (u 0, u 0) := by
    simpa only [hu0] using (analyticAt_chartGroupLaw X d).continuousAt
  have hprod := hFc.comp (f := fun p : ℝ × ℝ ↦ (u p.1, u p.2)) hp
  obtain ⟨K, S, hS, hK⟩ := (contDiffAt_chartVectorField X d v).exists_lipschitzOnWith
  have hmem1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), F (u p.1, u p.2) ∈ S := by
    apply hprod.tendsto.eventually
    change S ∈ 𝓝 (F (u 0, u 0))
    rw [hu0, hF0]
    exact hS
  have hmem2 : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), u (p.1 + p.2) ∈ S := by
    apply hsum.tendsto.eventually
    change S ∈ 𝓝 (u (0 + 0))
    rw [zero_add, hu0]
    exact hS
  have hcov : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0),
      fderiv ℂ F (u p.1, u p.2) (0, V (u p.2)) = V (F (u p.1, u p.2)) := by
    have h : ∀ᶠ q in 𝓝 (u 0, u 0),
        fderiv ℂ F q (0, V q.2) = V (F q) := by
      rw [hu0]
      exact chart_covariance X d v
    exact hp.tendsto.eventually h
  have hdiff : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), DifferentiableAt ℂ F (u p.1, u p.2) := by
    apply hp.tendsto.eventually
    simpa only [hu0] using (analyticAt_chartGroupLaw X d).eventually_analyticAt.mono
      (fun _ h ↦ h.differentiableAt)
  have hd2 : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), HasDerivAt u (V (u p.2)) p.2 :=
    (chartIntegralCurve_ode X d v).prod_inr_nhds (0 : ℝ)
  have hds : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0),
      HasDerivAt u (V (u (p.1 + p.2))) (p.1 + p.2) := by
    have hc : Tendsto (fun p : ℝ × ℝ ↦ p.1 + p.2) (𝓝 (0, 0)) (𝓝 0) := by
      simpa only [Pi.add_apply, zero_add] using!
        (continuousAt_fst.add continuousAt_snd (x := ((0 : ℝ), (0 : ℝ)))).tendsto
    exact hc.eventually (chartIntegralCurve_ode X d v)
  have htarget : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), u p.1 ∈ (identityChart X d).target := by
    apply (huc.comp (f := Prod.fst) continuousAt_fst).tendsto.eventually
    change (identityChart X d).target ∈ 𝓝 (u 0)
    rw [hu0]
    exact (identityChart X d).open_target.mem_nhds (chart_zero_target X d)
  have H : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0),
      (HasDerivAt (fun t ↦ F (u p.1, u t)) (V (F (u p.1, u p.2))) p.2 ∧
        F (u p.1, u p.2) ∈ S) ∧
      (HasDerivAt (fun t ↦ u (p.1 + t)) (V (u (p.1 + p.2))) p.2 ∧
        u (p.1 + p.2) ∈ S) ∧ u p.1 ∈ (identityChart X d).target := by
    filter_upwards [hmem1, hmem2, hcov, hdiff, hd2, hds, htarget]
      with p hm1 hm2 hcov hdiff hd2 hds ht
    refine ⟨⟨?_, hm1⟩, ⟨?_, hm2⟩, ht⟩
    · have h := (hdiff.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt p.2
        ((hasDerivAt_const p.2 (u p.1)).prodMk hd2)
      change HasDerivAt (fun t ↦ F (u p.1, u t))
        (fderiv ℂ F (u p.1, u p.2) (0, V (u p.2))) p.2 at h
      rw [hcov] at h
      exact h
    · have h := hds.scomp (h := fun t : ℝ ↦ p.1 + t) p.2
        ((hasDerivAt_id p.2).const_add p.1)
      simpa only [Function.comp_def, one_smul] using! h
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp H
  have hsmall (s t : ℝ) (hs : |s| < δ) (ht : |t| < δ) :=
    hball (show (s, t) ∈ ball (0, 0) δ by
      simpa only [mem_ball, Prod.dist_eq, dist_zero_right, Real.norm_eq_abs, max_lt_iff]
        using And.intro hs ht)
  refine ⟨δ, hδ, fun s t hs ht ↦ ?_⟩
  have hzero : |(0 : ℝ)| < δ := by simpa using hδ
  have heq : F (u s, u 0) = u (s + 0) := by
    rw [hu0, add_zero]
    exact chartGroupLaw_zero_right X d (hsmall s 0 hs hzero).2.2
  have huniq := ODE_solution_unique_of_mem_Ioo (v := fun _ ↦ V) (s := fun _ ↦ S)
    (f := fun t ↦ F (u s, u t)) (g := fun t ↦ u (s + t))
    (fun _ _ ↦ hK) (show (0 : ℝ) ∈ Ioo (-δ) δ by constructor <;> linarith)
    (fun t ht ↦ (hsmall s t hs (abs_lt.mpr ht)).1)
    (fun t ht ↦ (hsmall s t hs (abs_lt.mpr ht)).2.1) heq
  exact huniq (abs_lt.mp ht)

example (v : Fin d → ℂ) : ∃ δ > (0 : ℝ), ∀ s t : ℝ, |s| < δ → |t| < δ →
    chartGroupLaw X d (chartIntegralCurve X d v s, chartIntegralCurve X d v t) =
      chartIntegralCurve X d v (s + t) := chartIntegralCurve_local_add X d v

private theorem chart_lift_local_add (v : Fin d → ℂ) :
    ∃ δ > (0 : ℝ), ∀ s t : ℝ, |s| < δ → |t| < δ →
      (identityChart X d).symm (chartIntegralCurve X d v (s + t)) =
        (identityChart X d).symm (chartIntegralCurve X d v s) *
          (identityChart X d).symm (chartIntegralCurve X d v t) := by
  let u := chartIntegralCurve X d v
  have hu0 : u 0 = 0 := chartIntegralCurve_zero X d v
  have huc := (hasDerivAt_chartIntegralCurve X d v).continuousAt
  have hp : ContinuousAt (fun p : ℝ × ℝ ↦ (u p.1, u p.2)) (0, 0) :=
    (huc.comp (f := Prod.fst) continuousAt_fst).prodMk
      (huc.comp (f := Prod.snd) continuousAt_snd)
  have hprod : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0),
      (identityChart X d).symm (u p.1) * (identityChart X d).symm (u p.2) ∈
        (identityChart X d).source := by
    have h : ∀ᶠ q : (Fin d → ℂ) × (Fin d → ℂ) in 𝓝 (u 0, u 0),
        (identityChart X d).symm q.1 * (identityChart X d).symm q.2 ∈
          (identityChart X d).source := by
      rw [hu0]
      exact chart_product_source X d
    exact hp.tendsto.eventually h
  obtain ⟨ρ, hρ, hρball⟩ := Metric.mem_nhds_iff.mp hprod
  obtain ⟨δ, hδ, hδadd⟩ := chartIntegralCurve_local_add X d v
  refine ⟨min δ ρ, lt_min hδ hρ, fun s t hs ht ↦ ?_⟩
  have he := hδadd s t (lt_of_lt_of_le hs (min_le_left _ _))
    (lt_of_lt_of_le ht (min_le_left _ _))
  refine (congrArg (identityChart X d).symm he.symm).trans ?_
  apply (identityChart X d).left_inv
  have hb : (s, t) ∈ ball ((0 : ℝ), (0 : ℝ)) ρ := by
    simpa only [mem_ball, Prod.dist_eq, dist_zero_right, Real.norm_eq_abs, max_lt_iff] using
      And.intro (lt_of_lt_of_le hs (min_le_right _ _)) (lt_of_lt_of_le ht (min_le_right _ _))
  exact hρball (a := (s, t)) hb


/-- The chart integral curve lifted to the group, on an interval where its group law holds.

Source: constructed here from local ODE uniqueness and cancellation in the identity chart. -/
def chartLocalOneParameter (v : Fin d → ℂ) : LocalOneParameter (ComplexPoint X) where
  radius := (chart_lift_local_add X d v).choose
  radius_pos := (chart_lift_local_add X d v).choose_spec.1
  curve t := (identityChart X d).symm (chartIntegralCurve X d v t)
  map_zero := by rw [chartIntegralCurve_zero, chart_symm_zero]
  map_add s t hs ht _ := (chart_lift_local_add X d v).choose_spec.2 s t hs ht

example (v : Fin d → ℂ) (t : ℝ) : (chartLocalOneParameter X d v).curve t =
    (identityChart X d).symm (chartIntegralCurve X d v t) := rfl

/-- The continuous one-parameter subgroup with tangent vector `v`, constructed by subdivision.
Its domain is real time; its tangent vector is expressed in S10's complex coordinates.

Source: constructed here by Picard–Lindelöf and the subdivision construction of the Lie exponential. -/
def oneParameterSubgroup (v : Fin d → ℂ) : ℝ →+ Additive (ComplexPoint X) :=
  (chartLocalOneParameter X d v).extend

example (v : Fin d → ℂ) (s t : ℝ) :
    oneParameterSubgroup X d v (s + t) =
      oneParameterSubgroup X d v s + oneParameterSubgroup X d v t :=
  map_add (oneParameterSubgroup X d v) s t

/-- Every sufficiently fine positive subdivision gives the value of the subgroup.

Source: constructed here by common refinement of integer subdivisions. -/
theorem oneParameterSubgroup_eq_pow (v : Fin d → ℂ) (t : ℝ) {N : ℕ} (hN : 0 < N)
    (ht : |t / (N : ℝ)| < (chartLocalOneParameter X d v).radius) :
    (oneParameterSubgroup X d v t).toMul =
      (identityChart X d).symm (chartIntegralCurve X d v (t / (N : ℝ))) ^ N :=
  (chartLocalOneParameter X d v).extend_eq_pow t hN ht

example (v : Fin d → ℂ) (t : ℝ) {N : ℕ} (hN : 0 < N)
    (ht : |t / (N : ℝ)| < (chartLocalOneParameter X d v).radius) :
    (oneParameterSubgroup X d v t).toMul =
      (identityChart X d).symm (chartIntegralCurve X d v (t / (N : ℝ))) ^ N :=
  oneParameterSubgroup_eq_pow X d v t hN ht

/-- The constructed one-parameter subgroup is continuous on the entire real line.

Source: constructed here from local ODE continuity and continuity of a homomorphism at zero. -/
theorem continuous_oneParameterSubgroup (v : Fin d → ℂ) :
    Continuous (oneParameterSubgroup X d v) := by
  apply (chartLocalOneParameter X d v).continuous_extend
  have hc : ContinuousAt (identityChart X d).symm (chartIntegralCurve X d v 0) := by
    rw [chartIntegralCurve_zero]
    exact chart_symm_continuousAt X d
  exact hc.comp (hasDerivAt_chartIntegralCurve X d v).continuousAt

example (v : Fin d → ℂ) : Continuous (oneParameterSubgroup X d v) :=
  continuous_oneParameterSubgroup X d v

private theorem oneParameterSubgroup_lift (v : Fin d → ℂ) :
    (fun t ↦ (oneParameterSubgroup X d v t).toMul) =ᶠ[𝓝 0]
      (fun t ↦ (identityChart X d).symm (chartIntegralCurve X d v t)) := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (chartLocalOneParameter X d v).radius_pos]
    with t ht
  exact (chartLocalOneParameter X d v).extend_eq t (by simpa [Real.dist_eq] using ht)

/-- Near zero, the subgroup in the identity chart is the chosen integral curve.

Source: constructed here from extension of the local curve and the chart inverse identities. -/
theorem oneParameterSubgroup_chart (v : Fin d → ℂ) :
    (fun t ↦ identityChart X d (oneParameterSubgroup X d v t).toMul) =ᶠ[𝓝 0]
      chartIntegralCurve X d v := by
  have ht : ∀ᶠ t in 𝓝 0, chartIntegralCurve X d v t ∈ (identityChart X d).target := by
    apply (hasDerivAt_chartIntegralCurve X d v).continuousAt.tendsto.eventually
    change (identityChart X d).target ∈ 𝓝 (chartIntegralCurve X d v 0)
    rw [chartIntegralCurve_zero]
    exact (identityChart X d).open_target.mem_nhds (chart_zero_target X d)
  filter_upwards [oneParameterSubgroup_lift X d v, ht] with t he ht
  rw [he, (identityChart X d).right_inv ht]

example (v : Fin d → ℂ) :
    (fun t ↦ identityChart X d (oneParameterSubgroup X d v t).toMul) =ᶠ[𝓝 0]
      chartIntegralCurve X d v := oneParameterSubgroup_chart X d v

/-- The subgroup has the prescribed chart derivative at the identity.

Source: constructed here from Picard–Lindelöf's initial velocity. -/
theorem hasDerivAt_oneParameterSubgroup_chart (v : Fin d → ℂ) :
    HasDerivAt (fun t ↦ identityChart X d (oneParameterSubgroup X d v t).toMul) v 0 :=
  (hasDerivAt_chartIntegralCurve X d v).congr_of_eventuallyEq (oneParameterSubgroup_chart X d v)

example (v : Fin d → ℂ) :
    HasDerivAt (fun t ↦ identityChart X d (oneParameterSubgroup X d v t).toMul) v 0 :=
  hasDerivAt_oneParameterSubgroup_chart X d v

/-- The subgroup is `C¹` in the identity chart near zero.

Source: constructed here from the local ODE and analyticity of the vector field. -/
theorem contDiffAt_oneParameterSubgroup_chart (v : Fin d → ℂ) :
    ContDiffAt ℝ 1 (fun t ↦ identityChart X d (oneParameterSubgroup X d v t).toMul) 0 :=
  (chartIntegralCurve_contDiffAt X d v).congr_of_eventuallyEq (oneParameterSubgroup_chart X d v)

example (v : Fin d → ℂ) :
    ContDiffAt ℝ 1 (fun t ↦ identityChart X d (oneParameterSubgroup X d v t).toMul) 0 :=
  contDiffAt_oneParameterSubgroup_chart X d v

private theorem chartVectorField_smul (a : ℝ) (v u : Fin d → ℂ) :
    chartVectorField X d (a • v) u = a • chartVectorField X d v u := by
  let D := fderiv ℂ (chartGroupLaw X d) (u, 0)
  change D (0, a • v) = a • D (0, v)
  have hp : ((0 : Fin d → ℂ), a • v) = a • ((0 : Fin d → ℂ), v) := by simp
  rw [hp]
  exact (D.restrictScalars ℝ).map_smul a (0, v)

private theorem chartIntegralCurve_zero_vector :
    chartIntegralCurve X d (0 : Fin d → ℂ) =ᶠ[𝓝 0] (fun _ ↦ 0) := by
  apply chartIntegralCurve_unique X d 0 (chartIntegralCurve_zero X d 0) rfl
    (chartIntegralCurve_ode X d 0)
  apply Filter.Eventually.of_forall
  intro t
  simpa only [chartVectorField_origin] using! hasDerivAt_const t (0 : Fin d → ℂ)

/-- The zero tangent vector gives the constant identity subgroup.

Source: constructed here by local ODE uniqueness and subdivision. -/
theorem oneParameterSubgroup_zero : oneParameterSubgroup X d (0 : Fin d → ℂ) = 0 := by
  apply real_addHom_ext_of_eventuallyEq
  filter_upwards [oneParameterSubgroup_lift X d 0, chartIntegralCurve_zero_vector X d]
    with t ht hu
  apply Additive.toMul.injective
  change (oneParameterSubgroup X d 0 t).toMul = 1
  rw [ht, hu, chart_symm_zero]

example (t : ℝ) : (oneParameterSubgroup X d (0 : Fin d → ℂ) t).toMul = 1 := by
  rw [oneParameterSubgroup_zero]
  rfl

private theorem chartIntegralCurve_smul (a : ℝ) (v : Fin d → ℂ) :
    chartIntegralCurve X d (a • v) =ᶠ[𝓝 0] (fun t ↦ chartIntegralCurve X d v (a * t)) := by
  apply chartIntegralCurve_unique X d (a • v) (chartIntegralCurve_zero X d (a • v))
    (by simpa using chartIntegralCurve_zero X d v) (chartIntegralCurve_ode X d (a • v))
  have hc : Tendsto (fun t : ℝ ↦ a * t) (𝓝 0) (𝓝 0) := by
    have h : ContinuousAt (fun t : ℝ ↦ a * t) 0 := continuousAt_const.mul continuousAt_id
    simpa using! h.tendsto
  filter_upwards [hc.eventually (chartIntegralCurve_ode X d v)] with t ht
  have hd := ht.scomp (h := fun t : ℝ ↦ a * t) t ((hasDerivAt_id t).const_mul a)
  simpa only [Function.comp_def, mul_one, chartVectorField_smul] using! hd

private def realTimeScale (a : ℝ) : ℝ →+ ℝ where
  toFun t := a * t
  map_zero' := mul_zero a
  map_add' := mul_add a

/-- Scaling the tangent vector by a real scalar rescales time by that scalar.

Source: constructed here by uniqueness of the rescaled ODE and extension from a neighborhood. -/
theorem oneParameterSubgroup_smul (a : ℝ) (v : Fin d → ℂ) (t : ℝ) :
    oneParameterSubgroup X d (a • v) t = oneParameterSubgroup X d v (a * t) := by
  have he : oneParameterSubgroup X d (a • v) =
      (oneParameterSubgroup X d v).comp (realTimeScale a) := by
    apply real_addHom_ext_of_eventuallyEq
    have hc : Tendsto (fun t : ℝ ↦ a * t) (𝓝 0) (𝓝 0) := by
      have h : ContinuousAt (fun t : ℝ ↦ a * t) 0 := continuousAt_const.mul continuousAt_id
      simpa using! h.tendsto
    filter_upwards [oneParameterSubgroup_lift X d (a • v),
      hc.eventually (oneParameterSubgroup_lift X d v), chartIntegralCurve_smul X d a v]
      with t h1 h2 h3
    apply Additive.toMul.injective
    change (oneParameterSubgroup X d (a • v) t).toMul =
      (oneParameterSubgroup X d v (a * t)).toMul
    rw [h1, h2, h3]
  exact DFunLike.congr_fun he t

example (a : ℝ) (v : Fin d → ℂ) (t : ℝ) :
    oneParameterSubgroup X d (a • v) t = oneParameterSubgroup X d v (a * t) :=
  oneParameterSubgroup_smul X d a v t

/-- Doubling the velocity doubles time.

Source: constructed here as the scalar-two specialization of ODE rescaling. -/
theorem oneParameterSubgroup_two (v : Fin d → ℂ) (t : ℝ) :
    oneParameterSubgroup X d ((2 : ℂ) • v) t = oneParameterSubgroup X d v (2 * t) := by
  simpa only [two_smul] using oneParameterSubgroup_smul X d (2 : ℝ) v t

example (v : Fin d → ℂ) (t : ℝ) :
    oneParameterSubgroup X d ((2 : ℂ) • v) t = oneParameterSubgroup X d v (2 * t) :=
  oneParameterSubgroup_two X d v t

private abbrev trivialOneParameterGroup : Over (Spec ↧ℂ) := 𝟙_ (Over (Spec ↧ℂ))

private instance : SmoothOfRelativeDimension 0 trivialOneParameterGroup.hom := by
  change SmoothOfRelativeDimension 0 (𝟙 (Spec ↧ℂ))
  infer_instance

example (v : Fin 0 → ℂ) : chartIntegralCurve trivialOneParameterGroup 0 v = 0 :=
  Subsingleton.elim _ _

example (v : Fin 0 → ℂ) : oneParameterSubgroup trivialOneParameterGroup 0 v = 0 := by
  apply AddMonoidHom.ext
  intro t
  apply Additive.toMul.injective
  exact Subsingleton.elim _ _

example (v : Fin 0 → ℂ) (t : ℝ) :
    (oneParameterSubgroup trivialOneParameterGroup 0 v t).toMul = 1 := Subsingleton.elim _ _

example (v : Fin 0 → ℂ) : Continuous (oneParameterSubgroup trivialOneParameterGroup 0 v) :=
  continuous_oneParameterSubgroup trivialOneParameterGroup 0 v

example (v : Fin 0 → ℂ) : HasDerivAt
    (fun t ↦ identityChart trivialOneParameterGroup 0
      (oneParameterSubgroup trivialOneParameterGroup 0 v t).toMul) v 0 :=
  hasDerivAt_oneParameterSubgroup_chart trivialOneParameterGroup 0 v

end
end HodgeLean.Foundations

#print axioms HodgeLean.Foundations.chartVectorField
#print axioms HodgeLean.Foundations.chartVectorField_origin
#print axioms HodgeLean.Foundations.contDiffAt_chartVectorField
#print axioms HodgeLean.Foundations.chartVectorField_picardLindelof
#print axioms HodgeLean.Foundations.exists_chartIntegralCurve
#print axioms HodgeLean.Foundations.chartIntegralCurve_unique
#print axioms HodgeLean.Foundations.contDiffAt_chartIntegralCurve

#print axioms HodgeLean.Foundations.chartIntegralCurve
#print axioms HodgeLean.Foundations.chartIntegralCurve_zero
#print axioms HodgeLean.Foundations.chartIntegralCurve_ode
#print axioms HodgeLean.Foundations.hasDerivAt_chartIntegralCurve
#print axioms HodgeLean.Foundations.chartIntegralCurve_contDiffAt

#print axioms HodgeLean.Foundations.chartIntegralCurve_local_add

#print axioms HodgeLean.Foundations.chartLocalOneParameter
#print axioms HodgeLean.Foundations.oneParameterSubgroup
#print axioms HodgeLean.Foundations.oneParameterSubgroup_eq_pow
#print axioms HodgeLean.Foundations.continuous_oneParameterSubgroup
#print axioms HodgeLean.Foundations.oneParameterSubgroup_chart
#print axioms HodgeLean.Foundations.hasDerivAt_oneParameterSubgroup_chart
#print axioms HodgeLean.Foundations.contDiffAt_oneParameterSubgroup_chart

#print axioms HodgeLean.Foundations.oneParameterSubgroup_zero
#print axioms HodgeLean.Foundations.oneParameterSubgroup_smul
#print axioms HodgeLean.Foundations.oneParameterSubgroup_two
