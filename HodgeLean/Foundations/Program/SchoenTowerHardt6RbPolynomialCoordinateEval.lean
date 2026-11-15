import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Data.Real.Basic

/-! Evaluation transports polynomial coordinate automorphisms to actual point coordinates. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_polynomial_coordinate_eval {σ : Type*}
    (T : MvPolynomial σ ℝ ≃ₐ[ℝ] MvPolynomial σ ℝ) (x : σ → ℝ)
    (p : MvPolynomial σ ℝ) :
    MvPolynomial.eval (fun i => MvPolynomial.eval x (T (MvPolynomial.X i))) p =
      MvPolynomial.eval x (T p) := by
  have h : (MvPolynomial.aeval x).comp T.toAlgHom =
      MvPolynomial.aeval (fun i => MvPolynomial.eval x (T (MvPolynomial.X i))) := by
    ext i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_eq_eval]
    rfl
  exact (congrArg (fun f : MvPolynomial σ ℝ →ₐ[ℝ] ℝ => f p) h).symm

end HodgeLean.Foundations.Program
