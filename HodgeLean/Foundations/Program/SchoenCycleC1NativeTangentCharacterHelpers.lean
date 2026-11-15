import HodgeLean.Foundations.Program.SchoenCycleC1NativeParameterCharacterHelpers
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Native analytic tangent characters from the actual local parameter -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter Topology
namespace HodgeLean.Foundations.Program

/-- The residue of the actual stalk parameter multiplier equals the native
analytic tangent character of the same fixed-point curve morphism. -/
theorem s2e_c1_native_parameter_multiplier_derivative
    (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom]
    (f : X ⟶ X) (p : ComplexPoint X) (hp : Point.map f p = p)
    (v : (X.left.presheaf.stalk p.underlying)ˣ)
    (hv : s2e_fixed_point_stalkPullback X.left f.left p.underlying
      (by simpa only [Point.underlying_map] using congrArg Point.underlying hp)
      (s2e_native_curve_parameter X p) = s2e_native_curve_parameter X p *
        (v : X.left.presheaf.stalk p.underlying)) :
    let C := localChart X 1 p
    fderiv ℂ (fun z : Fin 1 → ℂ => C (Point.map f (C.symm (C p + z))) 0 - C p 0)
      0 (fun _ => 1) = p.stalkHom.hom (v : X.left.presheaf.stalk p.underlying) := by
  let A := s2e_stalk_nativeAnalyticGerm X 1 p
  let C := localChart X 1 p
  let F := fun z : Fin 1 → ℂ => C (Point.map f (C.symm (C p + z))) 0 - C p 0
  have hr := congrArg A hv
  rw [map_mul, s2e_c1_native_parameter_analytic_germ] at hr
  have hF : Filter.Germ.ofFun F =
      (s2e_nativeAnalytic_coordinate 1 0).val *
        (A (v : X.left.presheaf.stalk p.underlying)).val :=
    (s2e_c1_native_parameter_pullback_analytic_germ X f p hp).symm.trans
      (congrArg Subtype.val hr)
  obtain ⟨g, hg, hG⟩ := (A (v : X.left.presheaf.stalk p.underlying)).property
  rw [← hG] at hF
  change Filter.Germ.ofFun F = Filter.Germ.ofFun (fun z : Fin 1 → ℂ => z 0 * g z) at hF
  have hderiv : HasFDerivAt (fun z : Fin 1 → ℂ => z 0 * g z)
      (g 0 • (ContinuousLinearMap.proj 0 : (Fin 1 → ℂ) →L[ℂ] ℂ)) 0 := by
    have hh := (ContinuousLinearMap.proj 0 : (Fin 1 → ℂ) →L[ℂ] ℂ).hasFDerivAt.mul
      hg.differentiableAt.hasFDerivAt
    change HasFDerivAt (fun z : Fin 1 → ℂ => z 0 * g z)
      ((0 : ℂ) • fderiv ℂ g 0 + g 0 •
        (ContinuousLinearMap.proj 0 : (Fin 1 → ℂ) →L[ℂ] ℂ)) 0 at hh
    simpa only [zero_smul, zero_add] using hh
  change fderiv ℂ F 0 (fun _ => 1) = _
  rw [(Filter.Germ.coe_eq.mp hF).fderiv_eq, hderiv.fderiv]
  change g 0 * 1 = _
  rw [mul_one]
  have hval : s2e_nativeAnalyticGerm_value 1
      (A (v : X.left.presheaf.stalk p.underlying)) = g 0 := by
    change Filter.Germ.liftOn (A (v : X.left.presheaf.stalk p.underlying)).val _ _ = _
    rw [← hG]
    rfl
  exact hval.symm.trans (s2e_stalk_nativeAnalyticGerm_value X 1 p _)

end HodgeLean.Foundations.Program
