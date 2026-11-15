import HodgeLean.Foundations.TubularEuler.RetainedProjectorRecoveryHelpers
import HodgeLean.Foundations.TubularEuler.FiniteDimensionalAnalyticImmersionHelpers
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Local projective coordinates on the retained scheme atlas

The formula retains the original chart and its arbitrary target point. The
scheme tangent comparison is separate from the affine projector calculation.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler

/-- Local affine formula for the restricted projector in a retained scheme chart.
The target equivalence records the change of matrix coordinates.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 1, section 2;
Hartshorne, Algebraic Geometry, II.8.
HC no distance; AV milestone no distance. -/
theorem quasiProjectiveProjector_retained_chart_formula
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] (d N : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (e : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ)))
    [IsImmersion e.left] (z : ComplexPoint X) (a : Fin d → ℂ)
    (ha : a ∈ (chartAt (Fin d → ℂ) z).target) :
    ∃ (c : (Fin d → ℂ) → (Fin N → ℂ))
      (L : (Fin (N+1) → Fin (N+1) → ℂ) ≃L[ℝ]
        (Fin (N+1) → Fin (N+1) → ℂ)),
      ContDiffAt ℝ ω c a ∧
      (fun b => quasiProjectiveProjector e ((chartAt (Fin d → ℂ) z).symm b))
        =ᶠ[𝓝 a] (fun b => L (affineHermitianProjector (c b))) := by
  exact retained_projector_ratio_chart_formula X d N e z a ha

example (a : Fin 1 → ℂ) :
    ∃ (c : (Fin 1 → ℂ) → (Fin 1 → ℂ))
      (L : (Fin 2 → Fin 2 → ℂ) ≃L[ℝ] (Fin 2 → Fin 2 → ℂ)),
      ContDiffAt ℝ ω c a ∧
      affineHermitianProjector =ᶠ[𝓝 a] (fun b => L (affineHermitianProjector (c b))) := by
  exact ⟨id, ContinuousLinearEquiv.refl ℝ _, contDiffAt_id,
    Filter.Eventually.of_forall (fun _ => rfl)⟩

/-- The scheme immersion has injective differential in any such affine expression.
Source: Hartshorne, Algebraic Geometry, II.8, tangent map of an immersion.
HC no distance; AV milestone no distance. -/
theorem quasiProjectiveImmersion_retained_coordinate_injective
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] (d N : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (e : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ)))
    [IsImmersion e.left] (z : ComplexPoint X) (a : Fin d → ℂ)
    (ha : a ∈ (chartAt (Fin d → ℂ) z).target)
    (c : (Fin d → ℂ) → (Fin N → ℂ))
    (L : (Fin (N+1) → Fin (N+1) → ℂ) ≃L[ℝ]
      (Fin (N+1) → Fin (N+1) → ℂ))
    (hc : ContDiffAt ℝ ω c a)
    (hformula : (fun b => quasiProjectiveProjector e ((chartAt (Fin d → ℂ) z).symm b))
      =ᶠ[𝓝 a] (fun b => L (affineHermitianProjector (c b)))) :
    Function.Injective (fderiv ℝ c a) := by
  have hcD : DifferentiableAt ℝ c a := hc.differentiableAt (by simp)
  have hpD : DifferentiableAt ℝ affineHermitianProjector (c a) :=
    (affineHermitianProjector_contDiff N).differentiable (by simp) (c a)
  have hg : Function.Injective (fderiv ℝ
      (fun b => quasiProjectiveProjector e ((chartAt (Fin d → ℂ) z).symm b)) a) :=
    retained_projector_derivative_injective X d N e z a ha
  rw [hformula.fderiv_eq] at hg
  have hchain : fderiv ℝ (fun b => L (affineHermitianProjector (c b))) a =
      L.toContinuousLinearMap.comp
        ((fderiv ℝ affineHermitianProjector (c a)).comp (fderiv ℝ c a)) := by
    rw [show (fun b => L (affineHermitianProjector (c b))) =
      L ∘ (affineHermitianProjector ∘ c) from rfl,
      fderiv_comp a L.differentiableAt (hpD.comp a hcD), L.fderiv,
      fderiv_comp a hpD hcD]
  rw [hchain] at hg
  intro u v huv
  apply hg
  change L ((fderiv ℝ affineHermitianProjector (c a)) ((fderiv ℝ c a) u)) =
    L ((fderiv ℝ affineHermitianProjector (c a)) ((fderiv ℝ c a) v))
  rw [huv]

/-- The affine projector preserves every injective coordinate derivative.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 1, section 2;
checked `affineHermitianProjector_fderiv_injective`.
HC no distance; AV milestone no distance. -/
theorem affineProjector_coordinate_derivative_injective (d N : ℕ)
    (c : (Fin d → ℂ) → (Fin N → ℂ)) (a : Fin d → ℂ)
    (hc : DifferentiableAt ℝ c a) (hi : Function.Injective (fderiv ℝ c a))
    (L : (Fin (N+1) → Fin (N+1) → ℂ) ≃L[ℝ]
      (Fin (N+1) → Fin (N+1) → ℂ)) :
    Function.Injective (fderiv ℝ (fun b => L (affineHermitianProjector (c b))) a) := by
  rw [show (fun b => L (affineHermitianProjector (c b))) =
    L ∘ (affineHermitianProjector ∘ c) from rfl,
    fderiv_comp a L.differentiableAt
      (((affineHermitianProjector_contDiff N).differentiable (by simp) _).comp a hc),
    L.fderiv, fderiv_comp a
      ((affineHermitianProjector_contDiff N).differentiable (by simp) _) hc]
  exact L.injective.comp ((affineHermitianProjector_fderiv_injective N (c a)).comp hi)

/-- Analyticity of the literal projector expression at every original chart point.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 1, section 2.
HC no distance; AV milestone no distance. -/
theorem quasiProjectiveProjector_chart_contDiffAt
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] (d N : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (e : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ)))
    [IsImmersion e.left] (z : ComplexPoint X) (a : Fin d → ℂ)
    (ha : a ∈ (chartAt (Fin d → ℂ) z).target) :
    ContDiffAt ℝ ω
      (fun b => quasiProjectiveProjector e ((chartAt (Fin d → ℂ) z).symm b)) a := by
  obtain ⟨c, L, hc, he⟩ := quasiProjectiveProjector_retained_chart_formula X d N e z a ha
  exact (L.contDiff.contDiffAt.comp a
    ((affineHermitianProjector_contDiff N).contDiffAt.comp a hc)).congr_of_eventuallyEq he

/-- Derivative injectivity at arbitrary points of the retained chart target.
Source: Hartshorne, Algebraic Geometry, II.8; Griffiths–Harris, chapter 1, section 2.
HC no distance; AV milestone no distance. -/
theorem quasiProjectiveProjector_chart_fderiv_injective
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] (d N : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (e : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ)))
    [IsImmersion e.left] (z : ComplexPoint X) (a : Fin d → ℂ)
    (ha : a ∈ (chartAt (Fin d → ℂ) z).target) :
    Function.Injective (fderiv ℝ
      (fun b => quasiProjectiveProjector e ((chartAt (Fin d → ℂ) z).symm b)) a) := by
  obtain ⟨c, L, hc, he⟩ := quasiProjectiveProjector_retained_chart_formula X d N e z a ha
  rw [he.fderiv_eq]
  exact affineProjector_coordinate_derivative_injective d N c a
    (hc.differentiableAt (by simp))
    (quasiProjectiveImmersion_retained_coordinate_injective X d N e z a ha c L hc he) L

example (a : Fin 1 → ℂ) :
    Function.Injective (fderiv ℝ affineHermitianProjector a) :=
  affineHermitianProjector_fderiv_injective 1 a

end HodgeLean.Foundations.TubularEuler
