import HodgeLean.Foundations.Program.MilneTensorPairedNumerator
import HodgeLean.Foundations.Program.MilneTensorTotalCoordinates

noncomputable section
namespace HodgeLean.Foundations.Program

def m1b_pairCoordinates (d : ℕ) :
    (Fin 2 ⊕ Fin d → ℂ) ≃ₗ[ℂ] ((Fin 2 → ℂ) × (Fin d → ℂ)) :=
  LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin d) ℂ ℂ

theorem m1b_pairCoordinates_basis (d : ℕ) (i : Fin 2 ⊕ Fin d) :
    m1b_pairCoordinates d (Pi.single i 1) = m1b_pairBasisVector d i := by
  apply Prod.ext
  · funext j
    change (Pi.single i (1 : ℂ) : Fin 2 ⊕ Fin d → ℂ) (Sum.inl j) =
      (m1b_pairBasisVector d i).1 j
    cases i <;> simp [m1b_pairBasisVector, Pi.single_apply]
  · funext j
    change (Pi.single i (1 : ℂ) : Fin 2 ⊕ Fin d → ℂ) (Sum.inr j) =
      (m1b_pairBasisVector d i).2 j
    cases i <;> simp [m1b_pairBasisVector, Pi.single_apply]

theorem m1b_pairFormPoint_coordinates {d r n : ℕ}
    (Q : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ)
    (v : Fin n → Fin r → Fin 2 ⊕ Fin d → ℂ) :
    m1b_pairFormPoint
      (Q.toBilin'.compl₁₂ (m1b_pairCoordinates d).symm.toLinearMap
        (m1b_pairCoordinates d).symm.toLinearMap)
      (fun j c => m1b_pairCoordinates d (v j c)) =
        Sum.elim (fun ij => Q ij.1 ij.2) (fun jc => v jc.1 jc.2.1 jc.2.2) := by
  funext z
  cases z with
  | inl ij =>
    change Q.toBilin' ((m1b_pairCoordinates d).symm (m1b_pairBasisVector d ij.1))
      ((m1b_pairCoordinates d).symm (m1b_pairBasisVector d ij.2)) = Q ij.1 ij.2
    rw [← m1b_pairCoordinates_basis, ← m1b_pairCoordinates_basis,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    exact Matrix.toBilin'_single Q ij.1 ij.2
  | inr jc =>
    rcases jc with ⟨j, c, i | i⟩ <;> rfl

end HodgeLean.Foundations.Program
