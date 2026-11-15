import HodgeLean.Foundations.Program.SchoenSelectedGeometryIntegralModel
import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.AnalyticLeftInverse

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Set Filter Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A continuous lift through a smooth closed immersion is holomorphic when its composite is.
Source: analytic local left inverses obtained by lifting algebraic coordinate sections. -/
theorem s0_holomorphic_lift_of_closed_immersion
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    (X Y : Over (Spec ↧ℂ)) (d m : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension m Y.hom]
    (i : Y ⟶ X) [IsClosedImmersion i.left]
    (e : C → ComplexPoint Y) (he : Continuous e)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin d → ℂ) ω (fun x ↦ Point.map i (e x))) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin m → ℂ) ω e := by
  intro x
  let z := e x
  let φ := localChart Y m z
  let ψ := localChart X d (Point.map i z)
  have hz : z ∈ φ.source := mem_localChart_source Y m z
  have hy : Point.map i z ∈ ψ.source := mem_localChart_source X d _
  obtain ⟨L, hL, hl⟩ := exists_analytic_localLeftInverse_of_isClosedImmersion X Y i m d z
  rw [inclusionInComplexCharts_at_center] at hL
  have hLc : L (ψ (Point.map i z)) = φ z := by
    have hh := hl.eq_of_nhds
    simpa only [Function.comp_apply, inclusionInComplexCharts_at_center, id_eq] using hh
  let r : ComplexPoint X → ComplexPoint Y := fun w ↦ φ.symm (L (ψ w))
  have hψ : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω ψ (Point.map i z) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (Point.map i z)) hy
  have hφ : ContMDiffAt 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) ω φ.symm (φ z) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas z) (φ.map_source hz)
  have hr : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin m → ℂ) ω r (Point.map i z) :=
    hφ.comp_of_eq (hL.contDiffAt.contMDiffAt.comp (Point.map i z) hψ) hLc
  have hce : ContinuousAt (fun t ↦ φ (e t)) x := (φ.continuousAt hz).comp he.continuousAt
  have hsource : ∀ᶠ t in 𝓝 x, e t ∈ φ.source := he.continuousAt (φ.open_source.mem_nhds hz)
  have heq : e =ᶠ[𝓝 x] (fun t ↦ r (Point.map i (e t))) := by
    filter_upwards [hsource, hce.tendsto.eventually hl] with t ht hlt
    change L (ψ (Point.map i (φ.symm (φ (e t))))) = φ (e t) at hlt
    rw [φ.left_inv ht] at hlt
    change e t = φ.symm (L (ψ (Point.map i (e t))))
    rw [hlt, φ.left_inv ht]
  have hc : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin m → ℂ) ω
      (fun t ↦ r (Point.map i (e t))) x := hr.comp (g := r) (f := fun t ↦ Point.map i (e t)) x (hf x)
  exact hc.congr_of_eventuallyEq heq

#print axioms s0_holomorphic_lift_of_closed_immersion
end HodgeLean.Foundations.Program
