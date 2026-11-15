import HodgeLean.Foundations.Program.G32Native.PELPeriodComponentAction

noncomputable section
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- Scalar extension preserves the conjugation formula, including the side
on which the inverse occurs. -/
theorem pelPeriodMatrix_realConjugate (R : PELSplitReference)
    (g : pelRealIsometries R) (z : PELSplitDomain R) :
    pelPeriodMatrix R (pelRealConjugate R g z) =
      (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g.val)⁻¹ *
        pelPeriodMatrix R z * Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g.val := by
  apply Units.ext
  change (g.val.inv * z.J * g.val.val).map (algebraMap ℝ ℂ) = _
  rw [Matrix.map_mul, Matrix.map_mul]
  rfl

/-- Inverse conjugation is a right action: applying g followed by h is
conjugation by g*h. This rejects reversing the multiplication order. -/
theorem pelRealConjugate_mul (R : PELSplitReference)
    (g h : pelRealIsometries R) (z : PELSplitDomain R) :
    pelRealConjugate R h (pelRealConjugate R g z) =
      pelRealConjugate R (g * h) z := by
  have he : Function.Injective (PELSplitDomain.J (R := R)) := by
    intro a b hab
    cases a; cases b
    cases hab
    rfl
  apply he
  change h.val.inv * (g.val.inv * z.J * g.val.val) * h.val.val =
    (g.val * h.val).inv * z.J * (g.val * h.val).val
  change h.val.inv * (g.val.inv * z.J * g.val.val) * h.val.val =
    (h.val.inv * g.val.inv) * z.J * (g.val.val * h.val.val)
  simp only [mul_assoc]

#print axioms pelPeriodMatrix_realConjugate
#print axioms pelRealConjugate_mul
end HodgeLean.Foundations.Program.GeneralTypeIII
