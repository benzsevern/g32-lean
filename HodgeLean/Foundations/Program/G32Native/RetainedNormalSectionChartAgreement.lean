import HodgeLean.Foundations.Program.G32Native.RetainedMetricChartTransport
import HodgeLean.Foundations.Program.G32Native.RetainedHermitianNormalSection

/-! # Agreement of metric normal sections in ambient charts -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

/-- Sections with the retained evaluation and metric orthogonality equations
transform by the derivative of the actual ambient coordinate change.
Source: `retained_metric_normal_vector_change_chart` and
`retained_metric_normal_vector_exists_unique`. -/
theorem retained_normal_sections_change_chart
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (g : ChartHermitianMetric (ComplexPoint X) d)
    (A : X.left.Opens) (hA : IsAffineOpen A) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ A)) (z z' : ComplexPoint X)
    (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source)
    (hz' : Point.map j x ∈ (chartAt (Fin d → ℂ) z').source)
    (hD' : Function.Injective (retainedAffineConormalDifferential X Y j d A hA x hx z' hz'))
    (L L' : i1_normalFibre j.left x →ₗ[ℂ] (Fin d → ℂ))
    (hL : ∀ n, (∀ a, retainedAffineConormalDifferential X Y j d A hA x hx z hz a (L n) = n a) ∧
      ∀ w, (∀ a, retainedAffineConormalDifferential X Y j d A hA x hx z hz a w = 0) →
        g.coefficient z ((chartAt (Fin d → ℂ) z) (Point.map j x)) (L n) w = 0)
    (hL' : ∀ n, (∀ a, retainedAffineConormalDifferential X Y j d A hA x hx z' hz' a (L' n) = n a) ∧
      ∀ w, (∀ a, retainedAffineConormalDifferential X Y j d A hA x hx z' hz' a w = 0) →
        g.coefficient z' ((chartAt (Fin d → ℂ) z') (Point.map j x)) (L' n) w = 0) :
    ∀ n, fderiv ℝ (fun b => (chartAt (Fin d → ℂ) z')
      ((chartAt (Fin d → ℂ) z).symm b)) ((chartAt (Fin d → ℂ) z) (Point.map j x)) (L n) = L' n := by
  intro n
  obtain ⟨u, hu, huniq⟩ := retained_metric_normal_vector_exists_unique
    X Y j d g A hA x hx z' hz' hD' n
  exact (huniq _ (retained_metric_normal_vector_change_chart
    X Y j d g A hA x hx z z' hz hz' n (L n) (hL n))).trans (huniq _ (hL' n)).symm

#print axioms retained_normal_sections_change_chart
end HodgeLean.Foundations.TubularEuler
