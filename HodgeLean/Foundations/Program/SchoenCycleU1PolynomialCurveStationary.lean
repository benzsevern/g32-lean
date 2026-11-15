import HodgeLean.Foundations.Program.SchoenCycleU1PolynomialCurveJets
import HodgeLean.Foundations.Program.SchoenCycleU1ConstantDualPoint

/-! # Stationary actual polynomial scheme curves -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- A constant actual dual restriction forces all regular-section derivatives
of a polynomial scheme curve to vanish.
Source: Hartshorne, Algebraic Geometry, II.8, tangent vectors and derivations. -/
theorem s2e_u1_polynomialCurve_stationary
    (X : Over (Spec ↧ℂ)) (f : s2e_u1_specOver (Polynomial ℂ) ⟶ X)
    (hstationary : s2e_u1_polynomialDualParameter ≫ f =
      s2e_u1_constantDualPoint X (Point.map f (s2e_u1_polynomialParameterPoint 0)))
    (U : X.left.Opens)
    (h0 : (Point.map f (s2e_u1_polynomialParameterPoint 0)).underlying ∈ U)
    (a : Γ(X.left, U)) :
    deriv (fun t => Point.evaluate U a
      (Point.map f (s2e_u1_polynomialParameterPoint t))) 0 = 0 := by
  rw [s2e_u1_polynomialCurve_section_derivative X f U h0 a]
  have he : s2e_u1_specSectionEvaluation X.left
      (s2e_u1_polynomialDualParameter ≫ f).left U
      (s2e_u1_polynomialCurve_dual_open X f U h0) a =
    s2e_u1_specSectionEvaluation X.left
      (s2e_u1_constantDualPoint X (Point.map f (s2e_u1_polynomialParameterPoint 0))).left U
      (s2e_u1_constantDualPoint_open X _ U h0) a := by
    congr 2
    exact congrArg (fun g => g.left) hstationary
  rw [he, s2e_u1_constantDualPoint_sectionEvaluation X _ U h0 a]
  rfl

end HodgeLean.Foundations.Program
