import HodgeLean.Foundations.Program.SchoenCycleU1NativeCurveJets
import HodgeLean.Foundations.Program.SchoenCycleNativeParameterEvaluation

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- The centered native coordinate curve has identity derivative in the
centered native chart. -/
theorem s2v_l1b_action_centered_native_identity_derivative
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    (p : ComplexPoint Y) :
    deriv (fun z => ComplexPoint.localChart Y 1 p (s2e_u1_nativeCurve Y p z) 0 -
      ComplexPoint.localChart Y 1 p p 0) 0 = 1 := by
  have he := s2e_centered_chart_evaluation (ComplexPoint.localChart Y 1 p) p
    (ComplexPoint.mem_localChart_source Y 1 p)
    (fun q => ComplexPoint.localChart Y 1 p q 0 - ComplexPoint.localChart Y 1 p p 0)
    (fun _ _ => rfl)
  change (fun z => ComplexPoint.localChart Y 1 p (s2e_u1_nativeCurve Y p z) 0 -
    ComplexPoint.localChart Y 1 p p 0) =ᶠ[𝓝 0] (fun z => z) at he
  rw [he.deriv_eq]
  exact (hasDerivAt_id (0 : ℂ)).deriv

end HodgeLean.Foundations.Program
