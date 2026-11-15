import HodgeLean.Foundations.Program.SchoenTowerL1bActionNativeGerm

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- The scalar derivative in the local rotation comparison equals the
native vector-coordinate derivative used by the coefficient-order lemmas. -/
theorem s2e_c1_native_scalar_derivative
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    (p : ComplexPoint Y) (f : Y ⟶ Y) (hfix : Point.map f p = p) :
    deriv (s2v_l1b_action_nativeCoordinate Y p f) 0 =
      let C := localChart Y 1 p
      fderiv ℂ (fun w : Fin 1 → ℂ =>
        C (Point.map f (C.symm (C p + w))) 0 - C p 0) 0 (fun _ => 1) := by
  let C := localChart Y 1 p
  let F : (Fin 1 → ℂ) → ℂ := fun w =>
    C (Point.map f (C.symm (C p + w))) 0 - C p 0
  let E := b6m_surfaceCoordinateEquiv.toContinuousLinearMap
  have hv := s2e_fixed_morphism_centered_coordinates_analytic Y 1 f p hfix
  have ha := ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 1)).analyticAt _).comp hv
  change AnalyticAt ℂ (fun w : Fin 1 → ℂ =>
    C (Point.map f (C.symm (w + C p))) 0 - C p 0) 0 at ha
  have hF : AnalyticAt ℂ F 0 := by
    convert ha using 1
    funext w
    rw [add_comm w (C p)]
  have hFe : HasFDerivAt F (fderiv ℂ F 0) (E 0) := by
    rw [map_zero]
    exact hF.differentiableAt.hasFDerivAt
  have hd := (hFe.comp 0 E.hasFDerivAt).hasDerivAt
  have heq : F ∘ E = s2v_l1b_action_nativeCoordinate Y p f := by
    funext z
    rfl
  rw [heq] at hd
  exact hd.deriv

end HodgeLean.Foundations.Program
