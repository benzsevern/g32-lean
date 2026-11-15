import HodgeLean.Foundations.TubularEuler.ImmersionChartMetricHelpers

/-! # Original chart derivatives of a real analytic immersion map

The same ambient map in two scheme charts has differentials related by the
actual chart transition derivative.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry Topology Filter
namespace HodgeLean.Foundations.TubularEuler

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem complexPoint_chart_map_fderiv_chain
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (f : ComplexPoint X → H)
    (hf : ∀ z, ContDiffOn ℝ ⊤ (fun a => f ((chartAt (Fin d → ℂ) z).symm a))
      (chartAt (Fin d → ℂ) z).target)
    (z z' p : ComplexPoint X)
    (hp : p ∈ (chartAt (Fin d → ℂ) z).source)
    (hp' : p ∈ (chartAt (Fin d → ℂ) z').source) :
    fderiv ℝ (fun a => f ((chartAt (Fin d → ℂ) z).symm a))
        ((chartAt (Fin d → ℂ) z) p) =
      (fderiv ℝ (fun a => f ((chartAt (Fin d → ℂ) z').symm a))
        ((chartAt (Fin d → ℂ) z') p)).comp
      (fderiv ℝ (fun a => (chartAt (Fin d → ℂ) z')
        ((chartAt (Fin d → ℂ) z).symm a)) ((chartAt (Fin d → ℂ) z) p)) := by
  let c := chartAt (Fin d → ℂ) z
  let c' := chartAt (Fin d → ℂ) z'
  change fderiv ℝ (fun a => f (c.symm a)) (c p) =
    (fderiv ℝ (fun a => f (c'.symm a)) (c' p)).comp
      (fderiv ℝ (fun a => c' (c.symm a)) (c p))
  have ha : c p ∈ (c.symm.trans c').source := by
    exact ⟨c.map_source hp, by
      change c.symm (c p) ∈ c'.source
      simpa only [c.left_inv hp] using hp'⟩
  have hT : DifferentiableAt ℝ (fun a => c' (c.symm a)) (c p) :=
    (ComplexPoint.analyticAt_localChart_transition X d z z' ha).restrictScalars.differentiableAt
  have hF : DifferentiableAt ℝ (fun a => f (c'.symm a)) (c' p) :=
    ((hf z').contDiffAt (c'.open_target.mem_nhds (c'.map_source hp'))).differentiableAt
      (by simp)
  have hn : ∀ᶠ a in 𝓝 (c p), c.symm a ∈ c'.source :=
    (c.continuousAt_symm (c.map_source hp)).eventually
      (c'.open_source.mem_nhds (by simpa only [c.left_inv hp] using hp'))
  have he : (fun a => f (c.symm a)) =ᶠ[𝓝 (c p)]
      (fun a => f (c'.symm (c' (c.symm a)))) := by
    filter_upwards [hn] with a ha
    rw [c'.left_inv ha]
  have hF' : DifferentiableAt ℝ (fun a => f (c'.symm a)) (c' (c.symm (c p))) := by
    simpa only [c.left_inv hp] using hF
  exact he.fderiv_eq.trans (by
    simpa only [Function.comp_def, c.left_inv hp] using fderiv_comp (c p) hF' hT)

def complexPointChartMetricOfAnalyticImmersion
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (f : ComplexPoint X → K)
    (hf : ∀ z, ContDiffOn ℝ ⊤ (fun a => f ((chartAt (Fin d → ℂ) z).symm a))
      (chartAt (Fin d → ℂ) z).target)
    (hinj : ∀ z a, a ∈ (chartAt (Fin d → ℂ) z).target →
      Function.Injective (fderiv ℝ (fun b => f ((chartAt (Fin d → ℂ) z).symm b)) a)) :
    ChartHermitianMetric (ComplexPoint X) d :=
  complexPointChartMetricOfImmersionDifferentials X d
    (fun z a => fderiv ℝ (fun b => f ((chartAt (Fin d → ℂ) z).symm b)) a)
    (fun z => (hf z).fderiv_of_isOpen (chartAt (Fin d → ℂ) z).open_target (by simp))
    hinj (complexPoint_chart_map_fderiv_chain X d f hf)

#print axioms complexPointChartMetricOfAnalyticImmersion

#print axioms complexPoint_chart_map_fderiv_chain

end HodgeLean.Foundations.TubularEuler
