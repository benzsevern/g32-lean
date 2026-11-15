import HodgeLean.Foundations.Program.G32Native.ConormalEvaluationSurjectivity
import HodgeLean.Foundations.Program.G32Native.PositiveMetricNormalVector
import HodgeLean.Foundations.TubularEuler.RetainedConormalDifferentialHelpers
import HodgeLean.Foundations.TubularEuler.NormalGeometryInputs

/-! # Metric representatives of the original dual-conormal fibre

The original affine differential and the supplied chart metric determine
the vector uniquely. No replacement fibre or basis is selected.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

/-- A functional on the retained conormal fibre has a unique representative
orthogonal to the kernel of its actual affine differential, for the supplied
metric in the same ambient chart.
Source: Hartshorne, Algebraic Geometry, II.8, dual conormal sequence;
Lee, Introduction to Smooth Manifolds, second edition, normal spaces in
the proof of Theorem 6.24; `positiveMetric_normal_vector_exists_unique`.
HC no distance; AV milestone no distance. -/
theorem retained_metric_normal_vector_exists_unique
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (g : ChartHermitianMetric (ComplexPoint X) d)
    (A : X.left.Opens) (hA : IsAffineOpen A) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ A)) (z : ComplexPoint X)
    (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source)
    (hD : Function.Injective (retainedAffineConormalDifferential X Y j d A hA x hx z hz))
    (n : i1_normalFibre j.left x) :
    ∃! v : Fin d → ℂ,
      (∀ a : i1_conormalFibre j.left x,
        retainedAffineConormalDifferential X Y j d A hA x hx z hz a v = n a) ∧
      (∀ w : Fin d → ℂ,
        (∀ a : i1_conormalFibre j.left x,
          retainedAffineConormalDifferential X Y j d A hA x hx z hz a w = 0) →
        g.coefficient z ((chartAt (Fin d → ℂ) z) (Point.map j x)) v w = 0) := by
  let D := retainedAffineConormalDifferential X Y j d A hA x hx z hz
  let B := (ContinuousLinearMap.coeLM ℂ).comp D
  let T : (Fin d → ℂ) →ₗ[ℂ] i1_normalFibre j.left x := B.flip
  have hT : Function.Surjective T := by
    intro m
    obtain ⟨v, hv⟩ := injective_covector_evaluation_surjective D hD m
    exact ⟨v, LinearMap.ext hv⟩
  let G : LinearMap.BilinForm ℝ (Fin d → ℂ) :=
    (ContinuousLinearMap.coeLM ℝ).comp
      (g.coefficient z ((chartAt (Fin d → ℂ) z) (Point.map j x))).toLinearMap
  have hpoint : (chartAt (Fin d → ℂ) z) (Point.map j x) ∈
      (chartAt (Fin d → ℂ) z).target := (chartAt (Fin d → ℂ) z).map_source hz
  obtain ⟨v, hv, huniq⟩ := positiveMetric_normal_vector_exists_unique G
    (g.symmetric z _ hpoint) (g.positive z _ hpoint) (T.restrictScalars ℝ) hT n
  refine ⟨v, ⟨?_, ?_⟩, ?_⟩
  · intro a
    exact LinearMap.congr_fun hv.1 a
  · intro w hw
    exact hv.2 w (LinearMap.ext hw)
  · intro w hw
    apply huniq
    refine ⟨LinearMap.ext hw.1, ?_⟩
    intro u hu
    exact hw.2 u (fun a => LinearMap.congr_fun hu a)

#print axioms retained_metric_normal_vector_exists_unique

end HodgeLean.Foundations.TubularEuler
