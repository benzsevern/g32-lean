import HodgeLean.Foundations.Program.G32Native.RetainedConormalChartTransport
import HodgeLean.Foundations.TubularEuler.NormalGeometryInputs

/-! # Actual chart covariance of retained metric normal vectors

Both the retained conormal evaluation and the original metric transition law
refer to the same ambient coordinate change.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

/-- The actual ambient coordinate derivative transports a metric normal vector
to the corresponding vector for the same retained dual-conormal functional.
The affine presentation is kept fixed in this comparison.
Source: `retainedAffineConormalDifferential_change_chart`, the defining
transition law of `ChartHermitianMetric`, and positive-metric nondegeneracy.
HC no distance; AV milestone no distance. -/
theorem retained_metric_normal_vector_change_chart
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (g : ChartHermitianMetric (ComplexPoint X) d)
    (A : X.left.Opens) (hA : IsAffineOpen A) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ A)) (z z' : ComplexPoint X)
    (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source)
    (hz' : Point.map j x ∈ (chartAt (Fin d → ℂ) z').source)
    (n : i1_normalFibre j.left x) (v : Fin d → ℂ)
    (hv : (∀ a : i1_conormalFibre j.left x,
      retainedAffineConormalDifferential X Y j d A hA x hx z hz a v = n a) ∧
      (∀ w : Fin d → ℂ,
        (∀ a : i1_conormalFibre j.left x,
          retainedAffineConormalDifferential X Y j d A hA x hx z hz a w = 0) →
        g.coefficient z ((chartAt (Fin d → ℂ) z) (Point.map j x)) v w = 0)) :
    let H := fderiv ℝ (fun b => (chartAt (Fin d → ℂ) z')
      ((chartAt (Fin d → ℂ) z).symm b)) ((chartAt (Fin d → ℂ) z) (Point.map j x))
    (∀ a : i1_conormalFibre j.left x,
      retainedAffineConormalDifferential X Y j d A hA x hx z' hz' a (H v) = n a) ∧
      (∀ w : Fin d → ℂ,
        (∀ a : i1_conormalFibre j.left x,
          retainedAffineConormalDifferential X Y j d A hA x hx z' hz' a w = 0) →
        g.coefficient z' ((chartAt (Fin d → ℂ) z') (Point.map j x)) (H v) w = 0) := by
  let p := Point.map j x
  let a := chartAt (Fin d → ℂ) z
  let b := chartAt (Fin d → ℂ) z'
  let F := fun t => b (a.symm t)
  let H := fderiv ℝ F (a p)
  let D := retainedAffineConormalDifferential X Y j d A hA x hx z hz
  let D' := retainedAffineConormalDifferential X Y j d A hA x hx z' hz'
  have hsource : a p ∈ (a.symm.trans b).source := by
    refine ⟨a.map_source hz, ?_⟩
    change a.symm (a p) ∈ b.source
    rwa [a.left_inv hz]
  have htr : AnalyticAt ℂ F (a p) :=
    ComplexPoint.analyticAt_localChart_transition X d z z' hsource
  have hR : H = (fderiv ℂ F (a p)).restrictScalars ℝ :=
    (htr.hasStrictFDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv
  have happ (u : Fin d → ℂ) : (fderiv ℂ F (a p)) u = H u := by
    rw [hR]
    rfl
  have hcov (s : i1_conormalFibre j.left x) (u : Fin d → ℂ) :
      D s u = D' s (H u) := by
    have h := congrArg (fun C : (Fin d → ℂ) →L[ℂ] ℂ => C u)
      (retainedAffineConormalDifferential_change_chart X Y j d A hA x hx z z' hz hz' s)
    change D s u = D' s ((fderiv ℂ F (a p)) u) at h
    rwa [happ] at h
  have hzH : ∀ u : Fin d → ℂ, H u = 0 → u = 0 := by
    intro u hu
    by_contra hne
    have hp := g.positive z (a p) (a.map_source hz) u hne
    have hm := g.transition z z' p hz hz' u u
    change _ = g.coefficient z' (b p) (H u) (H u) at hm
    rw [hu, map_zero] at hm
    exact (ne_of_gt hp) hm
  have hinj : Function.Injective H := by
    intro u w h
    apply sub_eq_zero.mp
    apply hzH
    rw [map_sub, h, sub_self]
  have hsurj : Function.Surjective H := LinearMap.injective_iff_surjective.mp hinj
  constructor
  · intro s
    exact (hcov s v).symm.trans (hv.1 s)
  · intro w hw
    obtain ⟨u, rfl⟩ := hsurj w
    have hu : ∀ s : i1_conormalFibre j.left x, D s u = 0 :=
      fun s => (hcov s u).trans (hw s)
    exact (g.transition z z' p hz hz' v u).symm.trans (hv.2 u hu)

#print axioms retained_metric_normal_vector_change_chart

end HodgeLean.Foundations.TubularEuler
