import HodgeLean.Foundations.TubularEuler.RetainedConormalDifferentialHelpers

/-! # Differential and metric data preceding normal germs

The affine presentation and the analytic differential are the specified maps.
Metric coefficients obey the actual chart transition law.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Topology Bundle
open HodgeLean.Adapters HodgeLean.Foundations.BundleThom
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler

/-- A smooth Hermitian metric in the original manifold charts, written as real bilinear forms.
The transition equation prevents independent choices of Euclidean metrics in different charts.
Source: Lee, Introduction to Smooth Manifolds, second edition, Theorem 13.3
and partitions of unity; Hermitian symmetrization by the complex structure.
HC no distance; AV milestone no distance. -/
structure ChartHermitianMetric (M : Type*) [TopologicalSpace M] (d : ℕ)
    [ChartedSpace (Fin d → ℂ) M] where
  coefficient : M → (Fin d → ℂ) →
    ((Fin d → ℂ) →L[ℝ] (Fin d → ℂ) →L[ℝ] ℝ)
  smooth : ∀ z, ContDiffOn ℝ ⊤ (coefficient z) (chartAt (Fin d → ℂ) z).target
  symmetric : ∀ z a, a ∈ (chartAt (Fin d → ℂ) z).target →
    ∀ u w, coefficient z a u w = coefficient z a w u
  positive : ∀ z a, a ∈ (chartAt (Fin d → ℂ) z).target →
    ∀ u, u ≠ 0 → 0 < coefficient z a u u
  hermitian : ∀ z a, a ∈ (chartAt (Fin d → ℂ) z).target →
    ∀ u w, coefficient z a (Complex.I • u) (Complex.I • w) = coefficient z a u w
  transition : ∀ z z' p, p ∈ (chartAt (Fin d → ℂ) z).source →
    p ∈ (chartAt (Fin d → ℂ) z').source → ∀ u w,
    let D := fderiv ℝ
      (fun a => (chartAt (Fin d → ℂ) z') ((chartAt (Fin d → ℂ) z).symm a))
      ((chartAt (Fin d → ℂ) z) p)
    coefficient z ((chartAt (Fin d → ℂ) z) p) u w =
      coefficient z' ((chartAt (Fin d → ℂ) z') p) (D u) (D w)

end HodgeLean.Foundations.TubularEuler
