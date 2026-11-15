import HodgeLean.Foundations.Program.SchoenCycleStep1PointEvaluation
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Basic

/-! # Evaluation near equal actual algebraic germs -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Equal actual algebraic germs evaluate equally on an analytic neighbourhood
of the specified complex point.
Source: Hartshorne, Algebraic Geometry, II.1 and II.2, stalks and regular sections;
HodgeConjecture, AlgebraicGeometry.Point.isOpen_overOpen. -/
theorem s2e_equal_germs_eventually_evaluate
    (X : Over (Spec ↧ℂ)) (x : ComplexPoint X)
    (U V : X.left.Opens) (hxU : x.underlying ∈ U) (hxV : x.underlying ∈ V)
    (s : Γ(X.left, U)) (t : Γ(X.left, V))
    (h : X.left.presheaf.germ U x.underlying hxU s =
      X.left.presheaf.germ V x.underlying hxV t) :
    Point.evaluate U s =ᶠ[nhds x] Point.evaluate V t := by
  obtain ⟨W, hxW, iWU, iWV, he⟩ :=
    X.left.presheaf.germ_eq x.underlying hxU hxV s t h
  have hopen := Point.isOpen_overOpen (X := X) W
  filter_upwards [hopen.mem_nhds hxW] with q hq
  rw [Point.evaluate_res (leOfHom iWU) s q hq, Point.evaluate_res (leOfHom iWV) t q hq]
  exact congrArg (fun r : Γ(X.left, W) => Point.evaluate W r q) he

end HodgeLean.Foundations.Program
