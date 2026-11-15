import HodgeLean.Foundations.Program.SchoenCycleC1ActualCurveEigenorderHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1NativeTangentCharacterHelpers

/-! # Actual rational orders and native analytic tangent characters -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter Topology
namespace HodgeLean.Foundations.Program

/-- The signed order of an actual curve rational eigenfunction relates its
eigenvalue to the actual analytic tangent character at the fixed point. -/
theorem s2e_c1_actual_curve_native_tangent_eigenorder
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (f : X ⟶ X) [IsIso f.left] (p : ComplexPoint X) (hp : Point.map f p = p)
    (z : X.left.functionField) (hz : z ≠ 0) (η : ℂ)
    (heig : s2e_step1_fieldPullback X.left f.left z =
      HodgeLean.Foundations.Curves.stalkC (genericPoint X.left) η * z) :
    let R := X.left.presheaf.stalk p.underlying
    let t := s2e_native_curve_parameter X p
    let C := localChart X 1 p
    let ξ := fderiv ℂ (fun w : Fin 1 → ℂ => C (Point.map f (C.symm (C p + w))) 0 - C p 0)
      0 (fun _ => 1)
    ∃ (u : Rˣ) (n : ℤ),
      z = algebraMap R X.left.functionField (u : R) * algebraMap R X.left.functionField t ^ n ∧
      ξ ^ n = η := by
  have hp₀ : f.left p.underlying = p.underlying := by
    simpa only [Point.underlying_map] using congrArg Point.underlying hp
  obtain ⟨v, u, n, hv, hu, hn⟩ := s2e_c1_actual_curve_rational_eigenorder X f p hp₀ z hz η heig
  refine ⟨u, n, hu, ?_⟩
  rw [s2e_c1_native_parameter_multiplier_derivative X f p hp v hv]
  exact hn

end HodgeLean.Foundations.Program
