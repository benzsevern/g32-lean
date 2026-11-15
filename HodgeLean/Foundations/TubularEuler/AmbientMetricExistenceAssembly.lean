import HodgeLean.Foundations.TubularEuler.RealAnalyticMetricPrerequisiteHelpers
import HodgeLean.Foundations.TubularEuler.ImmersionChartDerivativeHelpers
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Ambient metric assembly from a specified analytic immersion

The Euclidean map and its chart regularity and tangent injectivity are explicit
inputs. This assembly imports no general immersion existence statement.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler

/-- Pull back a specified Euclidean immersion and symmetrize its metric.
Source: Lee, Introduction to Smooth Manifolds, second edition, chapter 13.
HC no distance; AV milestone no distance. -/
theorem ambientMetric_from_global_analytic_existence
    (W : Over (Spec (CommRingCat.of ℂ))) [LocallyOfFiniteType W.hom]
    [QuasiCompact W.hom] [IsSeparated W.hom]
    {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
    (d : ℕ) [SmoothOfRelativeDimension d (Over.mk (v ≫ W.hom)).hom]
    (n : ℕ) (f : ComplexPoint (Over.mk (v ≫ W.hom)) → EuclideanSpace ℝ (Fin n))
    (hf : ∀ z, ContDiffOn ℝ ω (fun a => f ((chartAt (Fin d → ℂ) z).symm a))
      (chartAt (Fin d → ℂ) z).target)
    (hi : ∀ z a, a ∈ (chartAt (Fin d → ℂ) z).target →
      Function.Injective (fderiv ℝ (fun b => f ((chartAt (Fin d → ℂ) z).symm b)) a)) :
    Nonempty (ChartHermitianMetric (ComplexPoint (Over.mk (v ≫ W.hom))) d) := by
  let X := Over.mk (v ≫ W.hom)
  letI : SmoothOfRelativeDimension d X.hom :=
    ‹SmoothOfRelativeDimension d (Over.mk (v ≫ W.hom)).hom›
  exact ⟨complexPointChartMetricOfAnalyticImmersion X d f hf hi⟩

example
    (W : Over (Spec (CommRingCat.of ℂ))) [LocallyOfFiniteType W.hom]
    [QuasiCompact W.hom] [IsSeparated W.hom]
    {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
    [SmoothOfRelativeDimension 1 (Over.mk (v ≫ W.hom)).hom]
    (n : ℕ) (f : ComplexPoint (Over.mk (v ≫ W.hom)) → EuclideanSpace ℝ (Fin n))
    (hf : ∀ z, ContDiffOn ℝ ω (fun a => f ((chartAt (Fin 1 → ℂ) z).symm a))
      (chartAt (Fin 1 → ℂ) z).target)
    (hi : ∀ z a, a ∈ (chartAt (Fin 1 → ℂ) z).target →
      Function.Injective (fderiv ℝ (fun b => f ((chartAt (Fin 1 → ℂ) z).symm b)) a))
    (z : ComplexPoint (Over.mk (v ≫ W.hom)))
    (a : Fin 1 → ℂ) (ha : a ∈ (chartAt (Fin 1 → ℂ) z).target) :
    ∃ g : ChartHermitianMetric (ComplexPoint (Over.mk (v ≫ W.hom))) 1,
      0 < g.coefficient z a (fun _ => 1) (fun _ => 1) := by
  obtain ⟨g⟩ := ambientMetric_from_global_analytic_existence W v 1 n f hf hi
  refine ⟨g, g.positive z a ha _ ?_⟩
  intro h
  have hzero := congrFun h (0 : Fin 1)
  exact one_ne_zero hzero

#print axioms ambientMetric_from_global_analytic_existence

end HodgeLean.Foundations.TubularEuler
