import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPolynomialCoordinateEval
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Polynomial coordinate automorphisms induce actual Euclidean homeomorphisms. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_polynomial_coordinate_homeomorph {n : ℕ}
    (T : MvPolynomial (Fin n) ℝ ≃ₐ[ℝ] MvPolynomial (Fin n) ℝ) :
    ∃ h : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n),
      (∀ x i, h x i = MvPolynomial.eval (fun j => x j) (T (MvPolynomial.X i))) ∧
      (∀ x i, h.symm x i = MvPolynomial.eval (fun j => x j) (T.symm (MvPolynomial.X i))) ∧
      ∀ x p, MvPolynomial.eval (fun i => h x i) p =
        MvPolynomial.eval (fun i => x i) (T p) := by
  let h : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
    { toFun := fun x i => MvPolynomial.eval x (T (MvPolynomial.X i))
      invFun := fun x i => MvPolynomial.eval x (T.symm (MvPolynomial.X i))
      left_inv := by
        intro x
        funext i
        dsimp only
        rw [s2v_hardt6rb_polynomial_coordinate_eval, T.apply_symm_apply, MvPolynomial.eval_X]
      right_inv := by
        intro x
        funext i
        dsimp only
        rw [s2v_hardt6rb_polynomial_coordinate_eval, T.symm_apply_apply, MvPolynomial.eval_X]
      continuous_toFun := continuous_pi fun i => MvPolynomial.continuous_eval _
      continuous_invFun := continuous_pi fun i => MvPolynomial.continuous_eval _ }
  let e := PiLp.homeomorph 2 (fun _ : Fin n => ℝ)
  refine ⟨e.trans (h.trans e.symm), ?_, ?_, ?_⟩
  · intro x i; rfl
  · intro x i; rfl
  · intro x p
    exact s2v_hardt6rb_polynomial_coordinate_eval T _ p

end HodgeLean.Foundations.Program
