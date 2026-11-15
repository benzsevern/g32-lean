import HodgeLean.Foundations.Program.G32Native.PELPeriodMatrices

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- Change reference coordinates by a real quaternion-linear isometry.
Source: Abdulali, Annals 155 (2002), §§2.2–2.3, 3.2. -/
def pelPeriodConjugate (R : PELSplitReference)
    (g : Matrix.GeneralLinearGroup (Fin 12) ℝ)
    (hform : g.val.transpose *
      R.form.map (algebraMap ℚ ℝ) * g = R.form.map (algebraMap ℚ ℝ))
    (hcomm : ∀ d, g.val *
      (R.operator d).map (algebraMap ℚ ℝ) =
      (R.operator d).map (algebraMap ℚ ℝ) * g.val)
    (z : PELSplitDomain R) : PELSplitDomain R where
  J := g.inv * z.J * g.val
  square := by
    calc
      (g.inv * z.J * g.val) * (g.inv * z.J * g.val) =
          g.inv * (z.J * z.J) * g.val := by simp only [mul_assoc, ← mul_assoc g.val g.inv, g.val_inv, one_mul]
      _ = -1 := by rw [z.square]; simp
  isometry := by
    have hi := congrArg (fun A : Matrix (Fin 12) (Fin 12) ℝ =>
      g.inv.transpose * A * g.inv) hform
    have hi' : g.inv.transpose *
        R.form.map (algebraMap ℚ ℝ) * g.inv = R.form.map (algebraMap ℚ ℝ) := by
      have hc : g.inv.transpose * g.val.transpose = 1 := by
        rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one]
      apply hi.symm.trans
      calc
        g.inv.transpose * (g.val.transpose * R.form.map (algebraMap ℚ ℝ) * g.val) * g.inv =
            (g.inv.transpose * g.val.transpose) * R.form.map (algebraMap ℚ ℝ) * (g.val * g.inv) := by
              simp only [mul_assoc]
        _ = _ := by rw [hc, g.val_inv, one_mul, mul_one]
    calc
      (g.inv * z.J * g.val).transpose * R.form.map (algebraMap ℚ ℝ) * (g.inv * z.J * g.val) =
          g.val.transpose * z.J.transpose *
            (g.inv.transpose * R.form.map (algebraMap ℚ ℝ) * g.inv) * z.J * g.val := by
              simp only [Matrix.transpose_mul, mul_assoc]
      _ = _ := by
        rw [hi']
        have hz := congrArg
          (fun A : Matrix (Fin 12) (Fin 12) ℝ => g.val.transpose * A * g.val) z.isometry
        simpa only [mul_assoc] using hz.trans hform
  positive := by
    have he : R.form.map (algebraMap ℚ ℝ) * g.inv =
        g.val.transpose * R.form.map (algebraMap ℚ ℝ) := by
      have hh := congrArg (fun A : Matrix (Fin 12) (Fin 12) ℝ => A * g.inv) hform
      simpa only [mul_assoc, g.val_inv, mul_one] using hh.symm
    rw [← mul_assoc, ← mul_assoc, he, mul_assoc]
    have hp := (Matrix.IsUnit.posDef_star_left_conjugate_iff g.isUnit).mpr z.positive
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      mul_assoc] using hp
  commute := by
    intro d
    have hi : g.inv * (R.operator d).map (algebraMap ℚ ℝ) =
        (R.operator d).map (algebraMap ℚ ℝ) * g.inv :=
      (show Commute g.val _ from hcomm d).units_inv_left.eq
    calc
      g.inv * z.J * g.val * (R.operator d).map (algebraMap ℚ ℝ) =
          g.inv * z.J * ((R.operator d).map (algebraMap ℚ ℝ) * g.val) := by rw [mul_assoc, hcomm]
      _ = (R.operator d).map (algebraMap ℚ ℝ) * (g.inv * z.J * g.val) := by
        calc
          g.inv * z.J * ((R.operator d).map (algebraMap ℚ ℝ) * g.val) =
              g.inv * (z.J * (R.operator d).map (algebraMap ℚ ℝ)) * g.val := by simp only [mul_assoc]
          _ = g.inv * ((R.operator d).map (algebraMap ℚ ℝ) * z.J) * g.val := by rw [z.commute d]
          _ = _ := by rw [← mul_assoc g.inv, hi]; simp only [mul_assoc]

#print axioms pelPeriodConjugate
end HodgeLean.Foundations.Program.GeneralTypeIII
