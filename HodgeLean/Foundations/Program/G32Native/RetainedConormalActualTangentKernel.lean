import HodgeLean.Foundations.Program.G32Native.RetainedConormalTangentKernel
import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.AnalyticLeftInverse

/-! # The actual coordinate tangent supplies the retained conormal kernel

Analyticity and injectivity of the tangent map are supplied by the original
smooth closed immersion, without an additional tangent hypothesis.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

/-- The original smooth closed immersion supplies its analytic injective tangent
map and identifies its range with the original conormal evaluation kernel.
Source: Hartshorne, Algebraic Geometry, II.8, conormal sequence;
`ComplexPoint.exists_leftInverse_fderiv_inclusionInComplexCharts`.
HC no distance; AV milestone no distance. -/
theorem retained_conormal_kernel_eq_actual_tangent_range
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (m k : ℕ) [SmoothOfRelativeDimension (m + k) X.hom] [SmoothOfRelativeDimension m Y.hom]
    (A : X.left.Opens) (hA : IsAffineOpen A) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ A))
    (hD : Function.Injective (retainedAffineConormalDifferential X Y j (m + k) A hA x hx
      (Point.map j x) (mem_chart_source _ _)))
    (hRank : Module.finrank ℂ
      (retainedAffineConormalDifferential X Y j (m + k) A hA x hx
        (Point.map j x) (mem_chart_source _ _)).range = k) :
    let D := retainedAffineConormalDifferential X Y j (m + k) A hA x hx
      (Point.map j x) (mem_chart_source _ _)
    let T : (Fin (m + k) → ℂ) →ₗ[ℂ] i1_normalFibre j.left x :=
      ((ContinuousLinearMap.coeLM ℂ).comp D).flip
    T.ker = (fderiv ℂ (ComplexPoint.inclusionInComplexCharts X Y j m (m + k) x)
      ((chartAt (Fin m → ℂ) x) x)).toLinearMap.range := by
  apply retained_conormal_kernel_eq_tangent_range X Y j m k A hA x hx
    (Point.map j x) (mem_chart_source _ _) hD hRank
  · exact (ComplexPoint.analyticAt_inclusionInComplexCharts X Y j m (m + k) x).hasStrictFDerivAt.hasFDerivAt
  · obtain ⟨P, hP⟩ :=
      ComplexPoint.exists_leftInverse_fderiv_inclusionInComplexCharts X Y j m (m + k) x
    intro v w hvw
    have h := congrArg P hvw
    change (P.comp (fderiv ℂ (ComplexPoint.inclusionInComplexCharts X Y j m (m + k) x)
      ((chartAt (Fin m → ℂ) x) x))) v =
      (P.comp (fderiv ℂ (ComplexPoint.inclusionInComplexCharts X Y j m (m + k) x)
        ((chartAt (Fin m → ℂ) x) x))) w at h
    change P.comp (fderiv ℂ (ComplexPoint.inclusionInComplexCharts X Y j m (m + k) x)
      ((chartAt (Fin m → ℂ) x) x)) = ContinuousLinearMap.id ℂ (Fin m → ℂ) at hP
    rw [hP] at h
    exact h

#print axioms retained_conormal_kernel_eq_actual_tangent_range

end HodgeLean.Foundations.TubularEuler
