import HodgeLean.Foundations.TubularEuler.QuasiProjectiveRatioHelpers
import HodgeLean.Foundations.TubularEuler.AffineRegularEvaluationHelpers
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-! # Projective point recovery from a projector column

The diagonal entry supplies the affine normalization of its column.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology
open AlgebraicGeometry.ComplexPoint AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Foundations.Program
open scoped ContDiff
namespace HodgeLean.Foundations.TubularEuler

def projectorRecoveredPoint {N : ℕ} (i : Fin (N+1))
    (P : Fin (N+1) → Fin (N+1) → ℂ) :
    ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ))) :=
  chartAffineComplexPointMap i ((affineSpaceEquiv (Fin (N+1))).symm
    (fun j => P j i / P i i))

theorem projectorRecoveredPoint_coordinates {N : ℕ} (v : Fin (N+1) → ℂ)
    (hv : v ≠ 0) (i : Fin (N+1)) (hi : v i ≠ 0) :
    projectorRecoveredPoint i (hermitianProjector v) = vectorToComplexPoint v hv := by
  have he : (fun j => hermitianProjector v j i / hermitianProjector v i i) =
      (v i)⁻¹ • v := by
    ext j
    rw [hermitianProjector_ratio v i hi j]
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hone : (affineSpaceEquiv (Fin (N+1)))
      ((affineSpaceEquiv (Fin (N+1))).symm
        (fun j => hermitianProjector v j i / hermitianProjector v i i)) i = 1 := by
    rw [Equiv.apply_symm_apply, hermitianProjector_ratio v i hi i, div_self hi]
  unfold projectorRecoveredPoint
  rw [s2e_projective_affineChart_normalized_map i _ hone]
  simpa only [Equiv.apply_symm_apply, he] using
    vectorToComplexPoint_smul v hv (v i)⁻¹ (inv_ne_zero hi)

theorem projectiveProjector_diagonal_ne_zero (N : ℕ)
    (p : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ))))
    (i : Fin (N+1)) (hi : p ∈ Point.overOpen (s2e_standardProjectiveAffineOpen i).1) :
    projectiveHermitianProjector N p i i ≠ 0 := by
  obtain ⟨⟨v, hv⟩, rfl⟩ := surjective_vectorToComplexPoint p
  have hvi := (s2e_standardProjectiveAffineOpen_mem_iff v hv i).mp hi
  change projectiveHermitianProjector N
    (projectivizationToComplexPoint (Projectivization.mk ℂ v hv)) i i ≠ 0
  have he := congrFun (congrFun (projectiveHermitianProjector_coordinates v hv) i) i
  rw [he]
  intro h
  have hr := hermitianProjector_ratio v i hvi i
  rw [h, div_zero, div_self hvi] at hr
  exact zero_ne_one hr

theorem projectorRecoveredPoint_projective (N : ℕ)
    (p : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ))))
    (i : Fin (N+1)) (hi : p ∈ Point.overOpen (s2e_standardProjectiveAffineOpen i).1) :
    projectorRecoveredPoint i (projectiveHermitianProjector N p) = p := by
  obtain ⟨⟨v, hv⟩, rfl⟩ := surjective_vectorToComplexPoint p
  have hvi := (s2e_standardProjectiveAffineOpen_mem_iff v hv i).mp hi
  have he := projectiveHermitianProjector_coordinates v hv
  change projectorRecoveredPoint i
    (projectiveHermitianProjector N (projectivizationToComplexPoint (Projectivization.mk ℂ v hv))) = _
  rw [he]
  exact projectorRecoveredPoint_coordinates v hv i hvi

theorem matrix_column_ratios_contDiffAt {n : ℕ} (i : Fin n)
    (M : Fin n → Fin n → ℂ) (hM : M i i ≠ 0) :
    ContDiffAt ℝ ω (fun Q : Fin n → Fin n → ℂ => fun j => Q j i / Q i i) M := by
  apply contDiffAt_pi.mpr
  intro j
  have hnum : ContDiffAt ℝ ω (fun Q : Fin n → Fin n → ℂ => Q j i) M :=
    (contDiff_apply_apply ℝ ℂ j i).contDiffAt
  have hden : ContDiffAt ℝ ω (fun Q : Fin n → Fin n → ℂ => Q i i) M :=
    (contDiff_apply_apply ℝ ℂ i i).contDiffAt
  simp only [div_eq_mul_inv]
  exact hnum.mul (hden.inv hM)

theorem projective_affine_section_analyticAt {N : ℕ} (i : Fin (N+1))
    (U : (ProjectiveSpace (Fin (N+1)) (Spec ↧ℂ)).Opens)
    (s : Γ(ProjectiveSpace (Fin (N+1)) (Spec ↧ℂ), U))
    (v : Fin (N+1) → ℂ)
    (hv : chartAffineComplexPointMap i ((affineSpaceEquiv (Fin (N+1))).symm v) ∈
      Point.overOpen U) :
    AnalyticAt ℂ (fun w => Point.evaluate U s
      (chartAffineComplexPointMap i ((affineSpaceEquiv (Fin (N+1))).symm w))) v := by
  let f : Over.mk (complexAffineSpace (Fin (N+1)) ↘ Spec ↧ℂ) ⟶
      Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ)) :=
    Over.homMk (chartAffineToProjectiveSpace i) (chartAffineToProjectiveSpace_over i)
  have hv' : (affineSpaceEquiv (Fin (N+1))).symm v ∈ Point.overOpen (f.left ⁻¹ᵁ U) :=
    (Point.mem_overOpen_map_iff f _ U).mp hv
  have heq : (fun w => Point.evaluate U s
      (chartAffineComplexPointMap i ((affineSpaceEquiv (Fin (N+1))).symm w))) =
      (fun w => Point.evaluate (f.left ⁻¹ᵁ U) (f.left.app U s)
        ((affineSpaceEquiv (Fin (N+1))).symm w)) := by
    funext w
    exact Point.evaluate_map f U s _
  rw [heq]
  exact affine_regular_local_analytic (N+1) (f.left ⁻¹ᵁ U) (f.left.app U s) v hv'

theorem projector_recovered_section_contDiffAt {N : ℕ} (i : Fin (N+1))
    (M : Fin (N+1) → Fin (N+1) → ℂ) (hM : M i i ≠ 0)
    (U : (ProjectiveSpace (Fin (N+1)) (Spec ↧ℂ)).Opens)
    (s : Γ(ProjectiveSpace (Fin (N+1)) (Spec ↧ℂ), U))
    (hU : projectorRecoveredPoint i M ∈ Point.overOpen U) :
    ContDiffAt ℝ ω (fun P => Point.evaluate U s (projectorRecoveredPoint i P)) M := by
  have he := projective_affine_section_analyticAt i U s (fun j => M j i / M i i) hU
  have heR : ContDiffAt ℝ ω (fun w => Point.evaluate U s
      (chartAffineComplexPointMap i ((affineSpaceEquiv (Fin (N+1))).symm w)))
      (fun j => M j i / M i i) := he.contDiffAt.restrict_scalars ℝ
  exact heR.comp M (matrix_column_ratios_contDiffAt i M hM)

end HodgeLean.Foundations.TubularEuler
