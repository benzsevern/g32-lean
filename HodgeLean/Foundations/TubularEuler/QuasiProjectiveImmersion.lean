import HodgeLean.Foundations.TubularEuler.AnalyticImmersionChartConverseHelpers
import HodgeLean.Foundations.TubularEuler.QuasiProjectiveAtlasSteps
import HodgeLean.Foundations.TubularEuler.FiniteDimensionalAnalyticImmersionHelpers
import HodgeLean.Foundations.TubularEuler.AmbientMetricExistenceAssembly
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Euclidean immersion supplier for a specified quasi-projective presentation

The map is the homogeneous Hermitian projector restricted along the supplied
scheme immersion. The two scheme-atlas comparisons are isolated from Euclidean
coordinate transport and metric assembly.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler

/-- Real analytic regularity in the retained smooth scheme atlas.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 1, section 2,
standard affine charts; Hartshorne, Algebraic Geometry, II.8.
HC no distance; AV milestone no distance. -/
theorem quasiProjectiveProjector_chart_regular_aux
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] (d N : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (e : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ)))
    [IsImmersion e.left] :
    ContMDiff 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, Fin (N+1) → Fin (N+1) → ℂ) ω
      (quasiProjectiveProjector e) := by
  letI := complexPoint_isRealAnalyticManifold X d
  intro x
  rw [contMDiffAt_iff_source]
  have hc := quasiProjectiveProjector_chart_contDiffAt X d N e x
    ((chartAt (Fin d → ℂ) x) x) ((chartAt (Fin d → ℂ) x).map_source
      (mem_chart_source _ x))
  simpa only [mfld_simps, contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt, Function.comp_def] using hc

/-- Faithfulness of the real tangent map of the specified scheme immersion.
The affine projector derivative is `affineHermitianProjector_fderiv_injective`.
Source: Hartshorne, Algebraic Geometry, II.8, tangent maps of immersions;
Griffiths–Harris, Principles of Algebraic Geometry, chapter 1, section 2.
HC no distance; AV milestone no distance. -/
theorem quasiProjectiveProjector_differential_aux
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] (d N : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (e : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ)))
    [IsImmersion e.left] (x : ComplexPoint X) :
    Function.Injective
      (mfderiv 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, Fin (N+1) → Fin (N+1) → ℂ)
        (quasiProjectiveProjector e) x) := by
  letI := complexPoint_isRealAnalyticManifold X d
  exact analyticImmersion_mfderiv_injective_of_chart (quasiProjectiveProjector e)
    (quasiProjectiveProjector_chart_regular_aux X d N e)
    (quasiProjectiveProjector_chart_fderiv_injective X d N e) x

/-- Euclidean coordinates for the explicitly specified quasi-projective projector.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 1, section 2;
Lee, Introduction to Smooth Manifolds, second edition, chapter 13.
HC no distance; AV milestone no distance. -/
theorem quasiProjectiveEuclideanImmersion_exists
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] (d N : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (e : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ)))
    [IsImmersion e.left] :
    ∃ (n : ℕ) (f : ComplexPoint X → EuclideanSpace ℝ (Fin n)),
      (∀ z, ContDiffOn ℝ ω (fun a => f ((chartAt (Fin d → ℂ) z).symm a))
        (chartAt (Fin d → ℂ) z).target) ∧
      (∀ z a, a ∈ (chartAt (Fin d → ℂ) z).target → Function.Injective
        (fderiv ℝ (fun b => f ((chartAt (Fin d → ℂ) z).symm b)) a)) := by
  letI := complexPoint_isRealAnalyticManifold X d
  exact realAnalyticEuclideanImmersion_of_finiteDimensional_target
    (quasiProjectiveProjector e) (quasiProjectiveProjector_chart_regular_aux X d N e)
    (quasiProjectiveProjector_differential_aux X d N e)

/-- The quasi-projective supplier feeds the original metric assembly.
Source: Lee, Introduction to Smooth Manifolds, second edition, chapter 13.
HC no distance; AV milestone no distance. -/
theorem ambientMetric_of_quasiProjective
    (W : Over (Spec ↧ℂ)) [LocallyOfFiniteType W.hom]
    [QuasiCompact W.hom] [IsSeparated W.hom]
    {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
    (d N : ℕ) [SmoothOfRelativeDimension d (Over.mk (v ≫ W.hom)).hom]
    (e : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ)))
    [IsImmersion e.left] :
    Nonempty (ChartHermitianMetric (ComplexPoint (Over.mk (v ≫ W.hom))) d) := by
  let X := Over.mk (v ≫ W.hom)
  letI : LocallyOfFiniteType X.hom := by
    change LocallyOfFiniteType (v ≫ W.hom)
    infer_instance
  let a : X ⟶ W := Over.homMk v rfl
  letI : IsImmersion (a ≫ e).left := by
    change IsImmersion (v ≫ e.left)
    infer_instance
  obtain ⟨n, f, hf, hi⟩ := quasiProjectiveEuclideanImmersion_exists X d N (a ≫ e)
  exact ambientMetric_from_global_analytic_existence W v d n f hf hi

-- Interface examples below use the scheme-atlas steps; the independent evaluations
-- are in QuasiProjectiveIndependentChecks.
example (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [SmoothOfRelativeDimension 1 X.hom] (N : ℕ)
    (e : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ)))
    [IsImmersion e.left] (x : ComplexPoint X) :
    ∃ (n : ℕ) (f : ComplexPoint X → EuclideanSpace ℝ (Fin n)),
      fderiv ℝ (fun a => f ((chartAt (Fin 1 → ℂ) x).symm a))
        ((chartAt (Fin 1 → ℂ) x) x) (fun _ => 1) ≠ 0 := by
  obtain ⟨n, f, _, hi⟩ := quasiProjectiveEuclideanImmersion_exists X 1 N e
  refine ⟨n, f, ?_⟩
  have hinj := hi x _ ((chartAt (Fin 1 → ℂ) x).map_source (mem_chart_source _ x))
  intro h
  have hz := hinj (h.trans (map_zero _).symm)
  have := congrFun hz (0 : Fin 1)
  exact one_ne_zero this

example (W : Over (Spec ↧ℂ)) [LocallyOfFiniteType W.hom]
    [QuasiCompact W.hom] [IsSeparated W.hom]
    {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
    [SmoothOfRelativeDimension 1 (Over.mk (v ≫ W.hom)).hom] (N : ℕ)
    (e : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ)))
    [IsImmersion e.left] (x : ComplexPoint (Over.mk (v ≫ W.hom)))
    (a : Fin 1 → ℂ) (ha : a ∈ (chartAt (Fin 1 → ℂ) x).target) :
    ∃ g : ChartHermitianMetric (ComplexPoint (Over.mk (v ≫ W.hom))) 1,
      0 < g.coefficient x a (fun _ => 1) (fun _ => 1) := by
  obtain ⟨g⟩ := ambientMetric_of_quasiProjective W v 1 N e
  refine ⟨g, g.positive x a ha _ ?_⟩
  intro h
  have := congrFun h (0 : Fin 1)
  exact one_ne_zero this

#print axioms quasiProjectiveProjector_chart_regular_aux
#print axioms quasiProjectiveProjector_differential_aux
#print axioms quasiProjectiveEuclideanImmersion_exists
#print axioms ambientMetric_of_quasiProjective
end HodgeLean.Foundations.TubularEuler
