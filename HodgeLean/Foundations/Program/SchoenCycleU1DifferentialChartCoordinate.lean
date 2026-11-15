import HodgeLean.Foundations.Program.SchoenCycleU1SupportRegularCoordinate

/-! # Regular coordinates in the actual differential line chart -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Manifold
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- The actual point parametrization used by the native differential coefficient.
Source: HodgeLean, `HurwitzPrymRR_loc` and `b4cov_lineEquiv`. -/
def s2e_u1_differentialChartCurve
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom]
    (p : ComplexPoint Z) (z : ℂ) : ComplexPoint Z :=
  (extChartAt 𝓘(ℂ, Fin 1 → ℂ) p).symm
    (extChartAt 𝓘(ℂ, Fin 1 → ℂ) p p +
      b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) z)

/-- The differential line parametrization is the actual native coordinate
curve with an invertible linear change of its scalar parameter.
Source: HodgeLean, `b4cov_lineEquiv`; Mathlib, linearity of a continuous linear equivalence. -/
theorem s2e_u1_differentialChartCurve_reparam
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom]
    (p : ComplexPoint Z) (z : ℂ) :
    s2e_u1_differentialChartCurve Z p z = s2e_u1_nativeCurve Z p
      (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) 1 0 * z) := by
  change (localChart Z 1 p).symm
      (localChart Z 1 p p + b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) z) =
    (localChart Z 1 p).symm _
  congr 1
  ext i
  fin_cases i
  have hl : b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) z =
      z • b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [hl]
  change localChart Z 1 p p 0 + z * _ = localChart Z 1 p p 0 + _ * z
  rw [mul_comm z]
  rfl

/-- The scalar relating the two actual curve parametrizations is nonzero.
Source: HodgeLean, `b4cov_lineEquiv_one_ne_zero`. -/
theorem s2e_u1_differentialChartCurve_scale_ne_zero :
    b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) 1 0 ≠ 0 := by
  intro h
  apply b4cov_lineEquiv_one_ne_zero (Module.finrank_fin_fun (n := 1) ℂ)
  ext i
  rw [show i = 0 from Subsingleton.elim _ _]
  exact h

/-- A regular coordinate with nonzero native derivative also has nonzero
derivative in the exact scalar line used by the differential coefficient.
Source: HodgeLean, `b4cov_lineEquiv`; Mathlib, `HasDerivAt.comp`. -/
theorem s2e_u1_differentialChartCurve_regular_coordinate
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom]
    (p : ComplexPoint Z) (U : Z.left.Opens) (hp : p.underlying ∈ U)
    (s : Γ(Z.left, U))
    (hs : deriv (fun t => Point.evaluate U s (s2e_u1_nativeCurve Z p t)) 0 ≠ 0) :
    AnalyticAt ℂ (fun t => Point.evaluate U s (s2e_u1_differentialChartCurve Z p t)) 0 ∧
      deriv (fun t => Point.evaluate U s (s2e_u1_differentialChartCurve Z p t)) 0 ≠ 0 := by
  let β := b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) 1 0
  let f : ℂ → ℂ := fun t => Point.evaluate U s (s2e_u1_nativeCurve Z p t)
  have hf : AnalyticAt ℂ f 0 := (s2e_u1_nativeCurve_regular_sections Z p U hp).2 s
  have he : (fun t => Point.evaluate U s (s2e_u1_differentialChartCurve Z p t)) =
      (fun t => f (β * t)) := by
    funext t
    rw [s2e_u1_differentialChartCurve_reparam]
  rw [he]
  refine ⟨hf.comp_of_eq (analyticAt_const.mul analyticAt_id) (mul_zero β), ?_⟩
  have hd : HasDerivAt (fun t : ℂ => f (β * t)) (deriv f 0 * β) 0 := by
    have houter : HasDerivAt f (deriv f 0) (β * 0) := by
      simpa only [mul_zero] using hf.differentiableAt.hasDerivAt
    have hinner : HasDerivAt (fun t : ℂ => β * t) β 0 := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id (0 : ℂ)).const_mul β
    exact houter.comp 0 hinner
  rw [hd.deriv]
  exact mul_ne_zero hs s2e_u1_differentialChartCurve_scale_ne_zero

end HodgeLean.Foundations.Program
