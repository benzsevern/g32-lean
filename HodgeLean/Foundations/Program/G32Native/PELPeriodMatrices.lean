import HodgeLean.Foundations.Program.G32Native.PELSplitDomain

noncomputable section
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- The retained real complex structure as an invertible complex matrix.
Source: Abdulali, Annals of Mathematics 155 (2002), §2.2, pp. 917–918. -/
def pelPeriodMatrix (R : PELSplitReference) (z : PELSplitDomain R) :
    Matrix.GeneralLinearGroup (Fin 12) ℂ where
  val := z.J.map (algebraMap ℝ ℂ)
  inv := -(z.J.map (algebraMap ℝ ℂ))
  val_inv := by
    rw [mul_neg, ← Matrix.map_mul, z.square, Matrix.map_neg, Matrix.map_one, neg_neg] <;> simp
  inv_val := by
    rw [neg_mul, ← Matrix.map_mul, z.square, Matrix.map_neg, Matrix.map_one, neg_neg] <;> simp

#print axioms pelPeriodMatrix
end HodgeLean.Foundations.Program.GeneralTypeIII
