import HodgeLean.Foundations.Program.SchoenCycleStep1

/-! # Agreement of native and affine-chart section evaluation -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Native stalk evaluation equals the actual complex algebra evaluation on a chart.
Source: Hartshorne, Algebraic Geometry, II.2, germs and evaluation of sections. -/
theorem s2e_u1_pointEvaluation_eq_evaluate (X : Over (Spec ↧ℂ)) (U : X.left.Opens)
    (x : ComplexPoint X) (hx : x.underlying ∈ U) (s : Γ(X.left, U)) :
    s2e_step1_pointEvaluation X U x (s2e_step1_point_preimage X x U hx) s =
      Point.evaluate U s x := by
  rw [Point.evaluate, dif_pos hx]
  have he := Scheme.germ_stalkClosedPointTo (R := CommRingCat.of ℂ) x.left U hx
  have hs := congrArg (fun g : Γ(X.left, U) ⟶ CommRingCat.of ℂ => g.hom s) he
  exact hs.symm

end HodgeLean.Foundations.Program
