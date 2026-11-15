import HodgeLean.Foundations.Program.G32Native.RetainedNormalSectionChartAgreement
import HodgeLean.Foundations.Program.G32Native.EuclideanDisplacementChartTransport

/-! # Agreement of differentiated metric sections in ambient charts -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

/-- Metric sections for the same retained affine presentation give the same
Euclidean vector after differentiating the specified embedding, independently
of the ambient chart.
Source: `retained_normal_sections_change_chart` and
`euclidean_displacement_chart_derivative_transport`. -/
theorem retained_euclidean_sections_change_chart
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d n : ℕ) [SmoothOfRelativeDimension d X.hom]
    (g : ChartHermitianMetric (ComplexPoint X) d)
    (emb : ComplexPoint X → EuclideanSpace ℝ (Fin n))
    (hemb : ContMDiff 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω emb)
    (A : X.left.Opens) (hA : IsAffineOpen A) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ A)) (z z' : ComplexPoint X)
    (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source)
    (hz' : Point.map j x ∈ (chartAt (Fin d → ℂ) z').source)
    (hD' : Function.Injective (retainedAffineConormalDifferential X Y j d A hA x hx z' hz'))
    (L L' : i1_normalFibre j.left x →ₗ[ℂ] (Fin d → ℂ))
    (hL : ∀ u, (∀ a, retainedAffineConormalDifferential X Y j d A hA x hx z hz a (L u) = u a) ∧
      ∀ w, (∀ a, retainedAffineConormalDifferential X Y j d A hA x hx z hz a w = 0) →
        g.coefficient z ((chartAt (Fin d → ℂ) z) (Point.map j x)) (L u) w = 0)
    (hL' : ∀ u, (∀ a, retainedAffineConormalDifferential X Y j d A hA x hx z' hz' a (L' u) = u a) ∧
      ∀ w, (∀ a, retainedAffineConormalDifferential X Y j d A hA x hx z' hz' a w = 0) →
        g.coefficient z' ((chartAt (Fin d → ℂ) z') (Point.map j x)) (L' u) w = 0) :
    ∀ u, fderiv ℝ (fun c => emb ((chartAt (Fin d → ℂ) z).symm c))
        ((chartAt (Fin d → ℂ) z) (Point.map j x)) (L u) =
      fderiv ℝ (fun c => emb ((chartAt (Fin d → ℂ) z').symm c))
        ((chartAt (Fin d → ℂ) z') (Point.map j x)) (L' u) := by
  intro u
  rw [euclidean_displacement_chart_derivative_transport X d n emb hemb z z'
    (Point.map j x) hz hz']
  simp only [ContinuousLinearMap.comp_apply]
  rw [retained_normal_sections_change_chart X Y j d g A hA x hx z z' hz hz' hD' L L' hL hL']

#print axioms retained_euclidean_sections_change_chart
end HodgeLean.Foundations.TubularEuler
