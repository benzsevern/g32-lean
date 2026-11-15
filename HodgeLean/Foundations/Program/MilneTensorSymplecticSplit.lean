import HodgeLean.Foundations.Program.MilneTensorPairCoordinates
import HodgeLean.Foundations.Program.MilneTensorPlanePolynomial

noncomputable section
namespace HodgeLean.Foundations.Program

def m1b_symplecticSplitIndex (k : ℕ) :
    (Fin (k + 1) ⊕ Fin (k + 1)) ≃ (Fin 2 ⊕ (Fin k ⊕ Fin k)) where
  toFun := Sum.elim
    (fun i => Fin.cases (Sum.inl 0) (fun j => Sum.inr (Sum.inl j)) i)
    (fun i => Fin.cases (Sum.inl 1) (fun j => Sum.inr (Sum.inr j)) i)
  invFun := Sum.elim
    (fun i => if i = 0 then Sum.inl 0 else Sum.inr 0)
    (Sum.elim (fun j => Sum.inl j.succ) (fun j => Sum.inr j.succ))
  left_inv x := by
    cases x with
    | inl i => cases i using Fin.cases <;> rfl
    | inr i => cases i using Fin.cases <;> rfl
  right_inv x := by
    cases x with
    | inl i => fin_cases i <;> rfl
    | inr i => cases i <;> rfl

theorem m1b_standard_symplectic_apply (k : ℕ) (x y : Fin k ⊕ Fin k → ℂ) :
    (m1b_J k).toBilin' x y =
      ∑ i, (x (Sum.inl i) * y (Sum.inr i) - x (Sum.inr i) * y (Sum.inl i)) := by
  simp [Matrix.toBilin'_apply, m1b_J, Matrix.one_apply, Finset.sum_add_distrib, sub_eq_add_neg, add_comm]

end HodgeLean.Foundations.Program
