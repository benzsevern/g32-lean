import HodgeLean.Foundations.TubularEuler.ImmersionMetricFormHelpers
import HodgeLean.Foundations.TubularEuler.ComplexChartDerivativeHelpers

/-! # Metric assembly from compatible immersion differentials

The coefficient at each chart point is the Euclidean pullback along the specified
immersion differential, followed by Hermitian symmetrization.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.TubularEuler

variable {M H : Type*} [TopologicalSpace M] {d : ℕ}
  [ChartedSpace (Fin d → ℂ) M] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def chartHermitianMetricOfImmersionDifferentials
    (A : M → (Fin d → ℂ) → (Fin d → ℂ) →L[ℝ] H)
    (hA : ∀ z, ContDiffOn ℝ ⊤ (A z) (chartAt (Fin d → ℂ) z).target)
    (hinj : ∀ z a, a ∈ (chartAt (Fin d → ℂ) z).target → Function.Injective (A z a))
    (hchain : ∀ z z' p, p ∈ (chartAt (Fin d → ℂ) z).source →
      p ∈ (chartAt (Fin d → ℂ) z').source →
      A z ((chartAt (Fin d → ℂ) z) p) =
        (A z' ((chartAt (Fin d → ℂ) z') p)).comp
          (fderiv ℝ (fun a => (chartAt (Fin d → ℂ) z')
            ((chartAt (Fin d → ℂ) z).symm a)) ((chartAt (Fin d → ℂ) z) p)))
    (hcomplex : ∀ (z z' p : M), p ∈ (chartAt (Fin d → ℂ) z).source →
      p ∈ (chartAt (Fin d → ℂ) z').source → ∀ u,
      fderiv ℝ (fun a => (chartAt (Fin d → ℂ) z')
          ((chartAt (Fin d → ℂ) z).symm a)) ((chartAt (Fin d → ℂ) z) p)
          (Complex.I • u) =
        Complex.I • fderiv ℝ (fun a => (chartAt (Fin d → ℂ) z')
          ((chartAt (Fin d → ℂ) z).symm a)) ((chartAt (Fin d → ℂ) z) p) u) :
    ChartHermitianMetric M d where
  coefficient := fun z a => immersionHermitianForm (A z a)
  smooth := fun z => immersionHermitianForm_contDiffOn (hA z)
  symmetric := fun z a _ => immersionHermitianForm_symmetric (A z a)
  positive := fun z a ha => immersionHermitianForm_positive (A z a) (hinj z a ha)
  hermitian := fun z a _ => immersionHermitianForm_hermitian (A z a)
  transition := by
    intro z z' p hp hp' u w
    exact immersionHermitianForm_transport_real _ _ _ (hchain z z' p hp hp')
      (hcomplex z z' p hp hp') u w

def complexPointChartMetricOfImmersionDifferentials
    (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of ℂ)))
    (d : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension d X.hom]
    (A : AlgebraicGeometry.ComplexPoint X → (Fin d → ℂ) → (Fin d → ℂ) →L[ℝ] H)
    (hA : ∀ z, ContDiffOn ℝ ⊤ (A z) (chartAt (Fin d → ℂ) z).target)
    (hinj : ∀ z a, a ∈ (chartAt (Fin d → ℂ) z).target → Function.Injective (A z a))
    (hchain : ∀ z z' p, p ∈ (chartAt (Fin d → ℂ) z).source →
      p ∈ (chartAt (Fin d → ℂ) z').source →
      A z ((chartAt (Fin d → ℂ) z) p) =
        (A z' ((chartAt (Fin d → ℂ) z') p)).comp
          (fderiv ℝ (fun a => (chartAt (Fin d → ℂ) z')
            ((chartAt (Fin d → ℂ) z).symm a)) ((chartAt (Fin d → ℂ) z) p))) :
    ChartHermitianMetric (AlgebraicGeometry.ComplexPoint X) d :=
  chartHermitianMetricOfImmersionDifferentials A hA hinj hchain
    (complexPoint_chart_transition_fderiv_mul_I X d)

#print axioms complexPointChartMetricOfImmersionDifferentials

#print axioms chartHermitianMetricOfImmersionDifferentials

end HodgeLean.Foundations.TubularEuler
