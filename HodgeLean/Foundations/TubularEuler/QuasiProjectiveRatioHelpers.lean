import HodgeLean.Foundations.TubularEuler.ProjectiveHermitianProjector
import HodgeLean.Foundations.Program.SchoenCycleProjectiveSectionEvaluation
import HodgeLean.Foundations.Program.SchoenCycleProjectiveChartDomainPoints

/-! # Regular homogeneous ratios in the retained source atlas

Regular coordinate ratios are evaluated after pullback to the original scheme.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ComplexProjectiveSpace AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Program
open scoped TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.TubularEuler

def projectiveRatioSection {n : ℕ} (i j : Fin (n+1)) :
    Γ(ProjectiveSpace (Fin (n+1)) (Spec ↧ℂ), (s2e_standardProjectiveAffineOpen i).1) :=
  (s2e_standardProjectiveSectionRingEquiv i).symm
    (s2e_baseChangedChartAlgEquiv ℂ i ((1 : ℂ) ⊗ₜ[ℤ] chartCoordinate.{0} i j))

theorem projectiveRatioSection_evaluate {n : ℕ} (v : CoordinateSpace n)
    (hv : v ≠ 0) (i j : Fin (n+1)) (hi : v i ≠ 0) :
    Point.evaluate (s2e_standardProjectiveAffineOpen i).1 (projectiveRatioSection i j)
      (vectorToComplexPoint v hv) = v j / v i := by
  rw [s2e_standardProjectiveSection_evaluate v i hi]
  simp only [projectiveRatioSection, RingEquiv.apply_symm_apply, AlgEquiv.symm_apply_apply]
  simp only [s2e_standardProjectiveChartEvaluation, AlgHom.liftEquiv_tmul, one_smul]
  exact s2e_projective_chartCoordinate_eval v i j hi

theorem retained_projectiveRatio_analyticAt
    (X : Over (Spec ↧ℂ)) (d N : ℕ) [SmoothOfRelativeDimension d X.hom]
    (e : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ)))
    (z : ComplexPoint X) (a : Fin d → ℂ)
    (ha : a ∈ (localChart X d z).target) (i j : Fin (N+1))
    (hi : Point.map e ((localChart X d z).symm a) ∈
      Point.overOpen (s2e_standardProjectiveAffineOpen i).1) :
    AnalyticAt ℂ (fun b => Point.evaluate (s2e_standardProjectiveAffineOpen i).1
      (projectiveRatioSection i j) (Point.map e ((localChart X d z).symm b))) a := by
  simp_rw [Point.evaluate_map]
  exact analyticAt_localChart_symm_evaluate X d z ha
    (e.left ⁻¹ᵁ (s2e_standardProjectiveAffineOpen i).1)
    (e.left.app _ (projectiveRatioSection i j))
    ((Point.mem_overOpen_map_iff e _ _).mp hi)

theorem projectiveHermitianProjector_ratio_formula (N : ℕ)
    (p : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ))))
    (i : Fin (N+1)) (hi : p ∈ Point.overOpen (s2e_standardProjectiveAffineOpen i).1) :
    projectiveHermitianProjector N p = hermitianProjector (fun j =>
      Point.evaluate (s2e_standardProjectiveAffineOpen i).1 (projectiveRatioSection i j) p) := by
  obtain ⟨⟨v, hv⟩, rfl⟩ := surjective_vectorToComplexPoint p
  have hvi := (s2e_standardProjectiveAffineOpen_mem_iff v hv i).mp hi
  have he : (fun j => Point.evaluate (s2e_standardProjectiveAffineOpen i).1
      (projectiveRatioSection i j) (vectorToComplexPoint v hv)) = (v i)⁻¹ • v := by
    ext j
    rw [projectiveRatioSection_evaluate v hv i j hvi]
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [he, hermitianProjector_smul v _ (inv_ne_zero hvi)]
  exact projectiveHermitianProjector_coordinates v hv

end HodgeLean.Foundations.TubularEuler
