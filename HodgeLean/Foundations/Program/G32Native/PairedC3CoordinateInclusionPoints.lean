import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateInclusion
import HodgeLean.Foundations.Program.SchoenCycleS3LinearPoints

/-! # Original vectors under a projective coordinate inclusion -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace MvPolynomial
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Extend a retained coordinate vector by zero in every discarded coordinate. -/
def pairedC3CoordinateVectorLift {ι κ : Type} (e : κ ↪ ι) :
    (κ → ℂ) →ₗ[ℂ] (ι → ℂ) := by
  classical
  exact {
    toFun := fun u j => if h : j ∈ Set.range e then
      u ((Equiv.ofInjective e e.injective).symm ⟨j, h⟩) else 0
    map_add' := by
      intro u v
      funext j
      by_cases h : j ∈ Set.range e
      · simp only [dif_pos h, Pi.add_apply]
      · simp only [dif_neg h, Pi.add_apply, add_zero]
    map_smul' := by
      intro a u
      funext j
      by_cases h : j ∈ Set.range e
      · simp only [dif_pos h, Pi.smul_apply, RingHom.id_apply]
      · simp only [dif_neg h, Pi.smul_apply, RingHom.id_apply, smul_zero] }

/-- The original retained coordinate is unchanged. -/
theorem paired_c3_coordinate_vector_lift_apply {ι κ : Type} (e : κ ↪ ι)
    (u : κ → ℂ) (j : κ) : pairedC3CoordinateVectorLift e u (e j) = u j := by
  classical
  change (if h : e j ∈ Set.range e then
    u ((Equiv.ofInjective e e.injective).symm ⟨e j, h⟩) else 0) = u j
  rw [dif_pos (Set.mem_range_self j)]
  change u ((Equiv.ofInjective e e.injective).symm ((Equiv.ofInjective e e.injective) j)) = _
  rw [Equiv.symm_apply_apply]

/-- Extending by zero is injective on the original source vectors. -/
theorem paired_c3_coordinate_vector_lift_injective {ι κ : Type} (e : κ ↪ ι) :
    Function.Injective (pairedC3CoordinateVectorLift e) := by
  intro u v h
  funext j
  simpa only [paired_c3_coordinate_vector_lift_apply] using congrFun h (e j)

/-- Polynomial coordinate restriction evaluates on the original extended vector. -/
theorem paired_c3_coordinate_projection_eval {ι κ : Type} (e : κ ↪ ι)
    (u : κ → ℂ) (p : MvPolynomial ι ℂ) :
    eval u (pairedC3GradedCoordinateProjection e p) =
      eval (pairedC3CoordinateVectorLift e u) p := by
  classical
  have h : (eval u).comp (pairedC3GradedCoordinateProjection (A := ℂ) e).toRingHom =
      eval (pairedC3CoordinateVectorLift e u) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change eval u (killCompl e.injective (C c)) = eval (pairedC3CoordinateVectorLift e u) (C c)
      rw [killCompl_C, eval_C, eval_C]
    · intro j
      simp [pairedC3GradedCoordinateProjection, killCompl, pairedC3CoordinateVectorLift]
      split_ifs <;> simp only [eval_X, map_zero]

  exact congrArg (fun f => f p) h

/-- The original projective coordinate inclusion sends an evaluation point
  to evaluation at the vector extended by zero.
Source: Hartshorne, Algebraic Geometry, I.2, projective linear subspaces. -/
theorem paired_c3_polynomial_coordinate_inclusion_point {k n : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (u : Fin (k + 1) → ℂ) (hu : u ≠ 0) :
    pairedC3PolynomialCoordinateInclusion (A := ℂ) e (s2e_polynomialEvaluationPoint u hu) =
      s2e_polynomialEvaluationPoint (pairedC3CoordinateVectorLift e u)
        (fun hz => hu ((paired_c3_coordinate_vector_lift_injective e)
          (hz.trans (map_zero (pairedC3CoordinateVectorLift e)).symm))) := by
  have hne : pairedC3CoordinateVectorLift e u ≠ 0 := fun hz =>
    hu ((paired_c3_coordinate_vector_lift_injective e)
      (hz.trans (map_zero (pairedC3CoordinateVectorLift e)).symm))
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro d p hp
  change pairedC3GradedCoordinateProjection e p ∈
    (s2e_polynomialEvaluationPoint u hu).asHomogeneousIdeal ↔ _
  erw [s2e_polynomialEvaluationPoint_mem u hu _
      ((pairedC3GradedCoordinateProjection (A := ℂ) e).map_mem hp),
    s2e_polynomialEvaluationPoint_mem (pairedC3CoordinateVectorLift e u) hne p hp]
  erw [paired_c3_coordinate_projection_eval]

/-- The actual projective-space morphism has the same retained vector action. -/
theorem paired_c3_coordinate_inclusion_point {k n : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (u : Fin (k + 1) → ℂ) (hu : u ≠ 0) :
    ((s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).inv ≫
        pairedC3PolynomialCoordinateInclusion (A := ℂ) e ≫
        (s2_polynomialProjectiveSpaceIso ℂ (Fin (n + 1))).hom)
      (vectorToComplexPoint u hu).underlying =
      (vectorToComplexPoint (pairedC3CoordinateVectorLift e u)
        (fun hz => hu ((paired_c3_coordinate_vector_lift_injective e)
          (hz.trans (map_zero (pairedC3CoordinateVectorLift e)).symm)))).underlying := by
  change (s2_polynomialProjectiveSpaceIso ℂ (Fin (n + 1))).hom
    (pairedC3PolynomialCoordinateInclusion (A := ℂ) e
      (s2e_polynomialEvaluationPoint u hu)) = _
  rw [paired_c3_polynomial_coordinate_inclusion_point]
  exact (Scheme.homeoOfIso (s2_polynomialProjectiveSpaceIso ℂ (Fin (n + 1)))).apply_symm_apply _

#print axioms paired_c3_polynomial_coordinate_inclusion_point
#print axioms paired_c3_coordinate_inclusion_point
#print axioms paired_c3_coordinate_vector_lift_apply
#print axioms paired_c3_coordinate_vector_lift_injective
#print axioms paired_c3_coordinate_projection_eval
end HodgeLean.Foundations.Program.G32Native
