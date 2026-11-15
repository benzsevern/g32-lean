import HodgeLean.Foundations.Program.ParabolicPolarizationBridge

/-! # H1: the same-signature countermodel

The diagonal model `⟨1, 1, 1, -1, -1, -1⟩` on `K⁶`, `K = ℚ(√-3)`, has rank six and signature
`(3, 3)`, as `hp_h0Form` does, but determinant class `[-1] ≠ [-2]`, since `2` is not a norm
from `K`. So it is not isometric to `hp_h0Form`, and no basis gives it the Gram matrix
`g32H0 ζ`: the discriminant hypothesis of `hp_parabolic_of_disc` is not implied by rank and
signature. HC no distance; AV milestone no distance.
-/

noncomputable section
open Matrix
open HodgeLean.Papers HodgeLean.RealDefs
open HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program

/-- The entries of `⟨1, 1, 1, -1, -1, -1⟩` are nonzero. -/
theorem hp_diag_neg_one_ne_zero : ∀ i, (![1, 1, 1, -1, -1, -1] : Fin 6 → ℚ) i ≠ 0 := by
  intro i
  fin_cases i <;> norm_num

/-- **Rank six.** The countermodel lives on `K⁶` and is nondegenerate.
Source: `HermitianForm.diagForm_nondegenerate`. -/
theorem hp_diag_neg_one_rank :
    Module.finrank (QuadraticAlgebra ℚ (-3) 0) (Fin 6 → QuadraticAlgebra ℚ (-3) 0) = 6 ∧
      (diagForm (a := -3) (b := 0) ![1, 1, 1, -1, -1, -1]).Nondegenerate :=
  ⟨by simp, diagForm_nondegenerate hp_diag_neg_one_ne_zero⟩

/-- **Signature `(3, 3)`**, the signature of `hp_h0Form`.
Source: `HermitianForm.hermSignature_diagForm`. -/
theorem hp_diag_neg_one_hermSignature :
    hermSignature (diagForm (a := -3) (b := 0) ![1, 1, 1, -1, -1, -1]) = (3, 3) := by
  rw [hermSignature_diagForm (by norm_num)]
  have hp : {i : Fin 6 | 0 < (![1, 1, 1, -1, -1, -1] : Fin 6 → ℚ) i} =
      ↑({0, 1, 2} : Finset (Fin 6)) := by
    ext i; fin_cases i <;> norm_num
  have hn : {i : Fin 6 | (![1, 1, 1, -1, -1, -1] : Fin 6 → ℚ) i < 0} =
      ↑({3, 4, 5} : Finset (Fin 6)) := by
    ext i; fin_cases i <;> norm_num
  rw [hp, hn, Set.ncard_coe_finset, Set.ncard_coe_finset]
  rfl

/-- **Determinant class `[-1]`.**
Source: `HermitianForm.detClass_diagForm`. -/
theorem hp_diag_neg_one_detClass :
    detClass (diagForm (a := -3) (b := 0) ![1, 1, 1, -1, -1, -1]) (diagForm_isSymm _)
        (diagForm_nondegenerate hp_diag_neg_one_ne_zero) =
      ((Units.mk0 (-1 : ℚ) (by norm_num) : ℚˣ) :
        ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) := by
  rw [detClass_diagForm hp_diag_neg_one_ne_zero]
  congr 1
  ext
  norm_num [Fin.prod_univ_succ]

/-- **`[-1] ≠ [-2]`**: their quotient `2` is not a norm, `x² + 3y² = 2` having no rational
solution.
Source: `HermitianForm.class_two_ne_one` (`HermitianForm.lean`, the classes of `ℚ(√-3)`). -/
theorem hp_class_neg_one_ne_neg_two :
    ((Units.mk0 (-1 : ℚ) (by norm_num) : ℚˣ) :
        ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) ≠ classNegTwo := by
  intro h
  rw [classNegTwo, QuotientGroup.eq] at h
  apply class_two_ne_one
  rw [QuotientGroup.eq_one_iff]
  convert h using 1
  ext
  norm_num

/-- **Not isometric to the printed form.** No `K`-linear equivalence carries `hp_h0Form` to the
countermodel, since the determinant classes differ (`hp_h0_detClass`).
Source: `HermitianClass.detClass_eq_of_equiv`. -/
theorem hp_diag_neg_one_not_isometric :
    ¬ ∃ g : (Fin 6 → QuadraticAlgebra ℚ (-3) 0) ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
        (Fin 6 → QuadraticAlgebra ℚ (-3) 0),
      ∀ x y, hp_h0Form (g x) (g y) = diagForm (a := -3) (b := 0) ![1, 1, 1, -1, -1, -1] x y := by
  rintro ⟨g, hg⟩
  apply hp_class_neg_one_ne_neg_two
  rw [← hp_diag_neg_one_detClass, ← hp_h0_detClass]
  exact HermitianClass.detClass_eq_of_equiv _ _ _ _ _ _ _ _ g hg

/-- **No basis gives the printed Gram matrix.** In no `K`-basis of `K⁶` is the Gram matrix of
the countermodel equal to `g32H0 ζ`.
Source: `hp_diag_neg_one_not_isometric`; Mathlib `Matrix.toLinearMapₛₗ₂_toMatrix₂`. -/
theorem hp_diag_neg_one_no_basis :
    ¬ ∃ e : Module.Basis (Fin 6) (QuadraticAlgebra ℚ (-3) 0) (Fin 6 → QuadraticAlgebra ℚ (-3) 0),
      LinearMap.toMatrix₂ e e (diagForm (a := -3) (b := 0) ![1, 1, 1, -1, -1, -1]) =
        g32H0 hp_zeta := by
  rintro ⟨e, he⟩
  refine hp_diag_neg_one_not_isometric ⟨e.equivFun, fun x y => ?_⟩
  rw [← Matrix.toLinearMapₛₗ₂_toMatrix₂ e e
    (diagForm (a := -3) (b := 0) ![1, 1, 1, -1, -1, -1]), he]
  simp [hp_h0Form, hp_matrixForm, Matrix.toLinearMapₛₗ₂_apply]

end HodgeLean.Foundations.Program
