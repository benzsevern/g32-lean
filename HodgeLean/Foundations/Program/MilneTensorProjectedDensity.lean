import HodgeLean.Foundations.Program.MilneTensorProjectedVariables

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι ζ : Type*} [Fintype ι] [DecidableEq ι]

theorem m1b_projected_polynomial_identity (ε : ℂ) (B : Matrix ι ι ℂ)
    (hB : (m1b_matrixFormProjection ε B).det ≠ 0)
    (P R : MvPolynomial ((ι × ι) ⊕ ζ) ℂ)
    (h : ∀ (Q : Matrix ι ι ℂ) (v : ζ → ℂ), (m1b_matrixFormProjection ε Q).det ≠ 0 →
      MvPolynomial.eval (Sum.elim (fun ij => Q ij.1 ij.2) v) P =
        MvPolynomial.eval (Sum.elim (fun ij => Q ij.1 ij.2) v) R) : P = R := by
  apply sub_eq_zero.mp
  apply m1b_polynomial_zero_on_principal_open (P - R)
    (m1b_projectedMatrixVariables (ι := ι) (ζ := ζ) ε).det
    (m1b_projectedMatrixVariables_det_ne_zero ε B hB)
  intro x hx
  let Q : Matrix ι ι ℂ := fun i j => x (Sum.inl (i, j))
  let v : ζ → ℂ := fun z => x (Sum.inr z)
  have he : Sum.elim (fun ij : ι × ι => Q ij.1 ij.2) v = x := by
    funext z
    cases z <;> rfl
  have hdet : (m1b_matrixFormProjection ε Q).det ≠ 0 := by
    rw [← he, RingHom.map_det, m1b_projectedMatrixVariables_eval] at hx
    exact hx
  rw [map_sub]
  exact sub_eq_zero.mpr (by simpa only [he] using h Q v hdet)

end HodgeLean.Foundations.Program
