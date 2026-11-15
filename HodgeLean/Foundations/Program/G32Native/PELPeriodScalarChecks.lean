import HodgeLean.Foundations.Program.G32Native.PELPeriodMatrices

noncomputable section
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- A real period complex structure cannot be scalar. This rejects both
real scalar signs and the zero matrix without a group-generation input. -/
theorem pelPeriod_J_ne_real_scalar (R : PELSplitReference) (z : PELSplitDomain R)
    (r : ℝ) : z.J ≠ r • (1 : Matrix (Fin 12) (Fin 12) ℝ) := by
  intro he
  have hs := z.square
  rw [he, smul_mul_smul, one_mul] at hs
  have hh := congrArg (fun M : Matrix (Fin 12) (Fin 12) ℝ => M 0 0) hs
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    Matrix.neg_apply] at hh
  nlinarith [sq_nonneg r]

/-- Scalar extension cannot turn the real period matrix into a complex
scalar: its diagonal entry determines a real scalar before extension. -/
theorem pelPeriodMatrix_ne_complex_scalar (R : PELSplitReference) (z : PELSplitDomain R)
    (c : ℂ) : (pelPeriodMatrix R z : Matrix (Fin 12) (Fin 12) ℂ) ≠
      c • (1 : Matrix (Fin 12) (Fin 12) ℂ) := by
  intro he
  have hc := congrArg (fun M : Matrix (Fin 12) (Fin 12) ℂ => M 0 0) he
  change (z.J 0 0 : ℂ) = _ at hc
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hc
  apply pelPeriod_J_ne_real_scalar R z (z.J 0 0)
  ext i j
  have hh := congrArg (fun M : Matrix (Fin 12) (Fin 12) ℂ => M i j) he
  change (z.J i j : ℂ) = _ at hh
  rw [← hc] at hh
  have hr := congrArg Complex.re hh
  simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    mul_ite, mul_one, mul_zero, apply_ite, Complex.ofReal_re, Complex.zero_re] using hr

#print axioms pelPeriod_J_ne_real_scalar
#print axioms pelPeriodMatrix_ne_complex_scalar
end HodgeLean.Foundations.Program.GeneralTypeIII
