import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic

noncomputable section
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- In dimension at least three, commuting with all elementary skew
matrices forces a scalar matrix. This is the coordinate calculation needed
for the centre in an orthonormal multiplicity basis. -/
theorem pel_skew_matrix_centralizer_scalar
    {ι k : Type*} [Fintype ι] [DecidableEq ι] [Field k]
    (third : ∀ i j : ι, ∃ l, l ≠ i ∧ l ≠ j)
    (X : Matrix ι ι k)
    (hX : ∀ i j : ι, X * (Matrix.single i j 1 - Matrix.single j i 1) =
      (Matrix.single i j 1 - Matrix.single j i 1) * X) (o : ι) :
    X = X o o • (1 : Matrix ι ι k) := by
  have hoff (a b : ι) (hab : a ≠ b) : X a b = 0 := by
    obtain ⟨c, hca, hcb⟩ := third a b
    have h := congrArg (fun M : Matrix ι ι k => M a c) (hX b c)
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply] at h
    rw [Matrix.mul_single_apply_same,
      Matrix.mul_single_apply_of_ne 1 c b a c hcb X,
      Matrix.single_mul_apply_of_ne 1 b c a c hab X,
      Matrix.single_mul_apply_of_ne 1 c b a c hca.symm X] at h
    simpa only [mul_one, sub_zero, sub_self] using h
  have hdiag (a b : ι) (hab : a ≠ b) : X a a = X b b := by
    have h := congrArg (fun M : Matrix ι ι k => M a b) (hX a b)
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply] at h
    rw [Matrix.mul_single_apply_same,
      Matrix.mul_single_apply_of_ne 1 b a a b hab.symm X,
      Matrix.single_mul_apply_same,
      Matrix.single_mul_apply_of_ne 1 b a a b hab X] at h
    simpa only [mul_one, one_mul, sub_zero] using h
  ext a b
  by_cases hab : a = b
  · subst b
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    by_cases hao : a = o
    · subst a; rfl
    · exact hdiag a o hao
  · simp only [Matrix.smul_apply, Matrix.one_apply_ne hab, smul_eq_mul, mul_zero]
    exact hoff a b hab

#print axioms pel_skew_matrix_centralizer_scalar
end HodgeLean.Foundations.Program.GeneralTypeIII
