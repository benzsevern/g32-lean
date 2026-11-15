import HodgeLean.Foundations.Program.MilneTensorScalarNumerator

noncomputable section
namespace HodgeLean.Foundations.Program

def m1b_scalarCoordinates (d : ℕ) :
    (Unit ⊕ Fin d → ℂ) ≃ₗ[ℂ] (ℂ × (Fin d → ℂ)) where
  toFun v := (v (Sum.inl ()), fun i => v (Sum.inr i))
  invFun v := Sum.elim (fun _ => v.1) v.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := by
    funext i
    cases i with
    | inl i => cases i; rfl
    | inr i => rfl
  right_inv v := rfl

theorem m1b_scalarCoordinates_basis (d : ℕ) (i : Unit ⊕ Fin d) :
    m1b_scalarCoordinates d (Pi.single i 1) = m1b_scalarBasisVector d i := by
  apply Prod.ext
  · change (Pi.single i (1 : ℂ) : Unit ⊕ Fin d → ℂ) (Sum.inl ()) = (m1b_scalarBasisVector d i).1
    cases i <;> simp [m1b_scalarBasisVector, Pi.single_apply]
  · funext j
    change (Pi.single i (1 : ℂ) : Unit ⊕ Fin d → ℂ) (Sum.inr j) = (m1b_scalarBasisVector d i).2 j
    cases i <;> simp [m1b_scalarBasisVector, Pi.single_apply]

theorem m1b_scalarCoordinates_standard (d : ℕ) :
    (m1b_prodBilin (LinearMap.mul ℂ ℂ) (1 : Matrix (Fin d) (Fin d) ℂ).toBilin').compl₁₂
      (m1b_scalarCoordinates d).toLinearMap (m1b_scalarCoordinates d).toLinearMap =
        (1 : Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℂ).toBilin' := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change x (Sum.inl ()) * y (Sum.inl ()) +
    (1 : Matrix (Fin d) (Fin d) ℂ).toBilin' (fun i => x (Sum.inr i)) (fun i => y (Sum.inr i)) =
      (1 : Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℂ).toBilin' x y
  simp only [Matrix.toBilin'_apply', Matrix.one_mulVec, dotProduct,
    Fintype.sum_sum_type, Fintype.sum_unique]

end HodgeLean.Foundations.Program
