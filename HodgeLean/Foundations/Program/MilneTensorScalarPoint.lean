import HodgeLean.Foundations.Program.MilneTensorScalarCoordinates

noncomputable section
namespace HodgeLean.Foundations.Program

theorem m1b_scalarFormPoint_coordinates {d r n : ℕ}
    (Q : Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℂ)
    (v : Fin n → Fin r → Unit ⊕ Fin d → ℂ) :
    m1b_scalarFormPoint
      (Q.toBilin'.compl₁₂ (m1b_scalarCoordinates d).symm.toLinearMap
        (m1b_scalarCoordinates d).symm.toLinearMap)
      (fun j c => m1b_scalarCoordinates d (v j c)) =
        Sum.elim (fun ij => Q ij.1 ij.2) (fun jc => v jc.1 jc.2.1 jc.2.2) := by
  funext z
  cases z with
  | inl ij =>
    change Q.toBilin' ((m1b_scalarCoordinates d).symm (m1b_scalarBasisVector d ij.1))
      ((m1b_scalarCoordinates d).symm (m1b_scalarBasisVector d ij.2)) = Q ij.1 ij.2
    rw [← m1b_scalarCoordinates_basis, ← m1b_scalarCoordinates_basis,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    exact Matrix.toBilin'_single Q ij.1 ij.2
  | inr jc =>
    rcases jc with ⟨j, c, i | i⟩
    · cases i; rfl
    · rfl

end HodgeLean.Foundations.Program
