import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.NormalCoordinates
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Actual immersion normals and homogeneous coefficient kernels

The normal chart uses the derivative projection of the specified immersion.
The coefficient model retains a specified nonzero homogeneous vector.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- The normal producer at the specified point uses the algebraic derivative projection.
Source: HodgeConjecture, Definitions/AlgebraicGeometry/ClosedImmersion/NormalCoordinates,
closedImmersionDerivativeProjection. -/
def g32n_normalProducer (X Q : Over (Spec ↧ℂ)) (ι : Q ⟶ X) (k : ℕ)
    [SmoothOfRelativeDimension k Q.hom]
    [SmoothOfRelativeDimension (k + k) X.hom] [IsClosedImmersion ι.left]
    (x : ComplexPoint Q) :=
  closedImmersionNormalChart X Q ι k (k + k) x

/-- The actual normal coordinate has rank k in ambient dimension 2k. -/
theorem g32n_normal_rank (X Q : Over (Spec ↧ℂ)) (ι : Q ⟶ X) (k : ℕ)
    [SmoothOfRelativeDimension k Q.hom]
    [SmoothOfRelativeDimension (k + k) X.hom] [IsClosedImmersion ι.left]
    (x : ComplexPoint Q) :
    Module.finrank ℂ (closedImmersionDerivativeProjection X Q ι k (k + k) x).ker = k := by
  rw [closedImmersionNormalKernel_finrank]
  omega

/-- The same normal producer detects the entire immersion support on an open neighbourhood. -/
theorem g32n_normal_support (X Q : Over (Spec ↧ℂ)) (ι : Q ⟶ X) (k : ℕ)
    [SmoothOfRelativeDimension k Q.hom]
    [SmoothOfRelativeDimension (k + k) X.hom] [IsClosedImmersion ι.left]
    (x : ComplexPoint Q) :
    ∃ U : Set (ComplexPoint X), IsOpen U ∧ Point.map ι x ∈ U ∧
      ∀ y ∈ U, y ∈ Set.range (Point.map ι) ↔
        ((g32n_normalProducer X Q ι k x).symm
          (localChart X (k + k) (Point.map ι x) y)).2 = 0 := by
  exact exists_open_normalCriterion X Q ι k (k + k) x

/-- Evaluation of a dual coefficient vector on the specified homogeneous vector. -/
def g32n_coefficientEvaluation (k : ℕ) (v : Fin (k + 1) → ℂ) :
    Module.Dual ℂ (Fin (k + 1) → ℂ) →ₗ[ℂ] ℂ :=
  Module.Dual.eval ℂ (Fin (k + 1) → ℂ) v

/-- The coefficient kernel is exactly the annihilator of the retained homogeneous line. -/
theorem g32n_coefficient_kernel (k : ℕ) (v : Fin (k + 1) → ℂ) :
    LinearMap.ker (g32n_coefficientEvaluation k v) =
      (Submodule.span ℂ {v}).dualAnnihilator := by
  ext f
  rw [LinearMap.mem_ker, Submodule.mem_dualAnnihilator]
  change f v = 0 ↔ ∀ w ∈ Submodule.span ℂ {v}, f w = 0
  constructor
  · intro h w hw
    have hs : Submodule.span ℂ {v} ≤ LinearMap.ker f := by
      rw [Submodule.span_le]
      intro a ha
      obtain rfl := Set.mem_singleton_iff.mp ha
      exact h
    exact hs hw
  · intro h
    exact h v (Submodule.subset_span (Set.mem_singleton v))

/-- A nonzero homogeneous vector gives a coefficient kernel of rank k. -/
theorem g32n_coefficient_kernel_rank (k : ℕ) (v : Fin (k + 1) → ℂ)
    (hv : v ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (g32n_coefficientEvaluation k v)) = k := by
  rw [g32n_coefficient_kernel]
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq (Submodule.span ℂ {v})
  rw [finrank_span_singleton hv, Module.finrank_pi, Fintype.card_fin] at h
  omega

/-- Evaluation written in the fixed ordered coefficient coordinates. -/
def g32n_coefficientFunctional (k : ℕ) (v : Fin (k + 1) → ℂ) :
    (Fin (k + 1) → ℂ) →L[ℂ] ℂ :=
  ∑ i, v i • ContinuousLinearMap.proj i

/-- The tangent kernel in fixed coefficient coordinates is the evaluation equation. -/
theorem g32n_coefficient_tangent_kernel (k : ℕ) (v a u : Fin (k + 1) → ℂ) :
    u ∈ LinearMap.ker (fderiv ℂ (g32n_coefficientFunctional k v) a).toLinearMap ↔
      ∑ i, v i * u i = 0 := by
  rw [(g32n_coefficientFunctional k v).fderiv]
  change (g32n_coefficientFunctional k v) u = 0 ↔ _
  simp only [g32n_coefficientFunctional, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

#print axioms g32n_coefficient_kernel_rank
#print axioms g32n_coefficient_tangent_kernel
#print axioms g32n_normalProducer
#print axioms g32n_normal_rank
#print axioms g32n_normal_support
#print axioms g32n_coefficientEvaluation
#print axioms g32n_coefficient_kernel
end HodgeLean.Foundations.Program
