import HodgeLean.Foundations.Program.MilneTensorPolynomial
import Mathlib.Data.Sym.Sym2

noncomputable section
namespace HodgeLean.Foundations.Program

def m1b_symmetricVariables (d : ℕ) :
    Matrix (Fin d) (Fin d) (MvPolynomial (Sym2 (Fin d)) ℂ) :=
  fun i j => MvPolynomial.X (Sym2.mk i j)

theorem m1b_symmetricVariables_transpose (d : ℕ) :
    (m1b_symmetricVariables d).transpose = m1b_symmetricVariables d := by
  apply Matrix.ext
  intro i j
  change (MvPolynomial.X (Sym2.mk j i) : MvPolynomial (Sym2 (Fin d)) ℂ) = MvPolynomial.X (Sym2.mk i j)
  rw [Sym2.eq_swap]

def m1b_symmetricEvaluation (d : ℕ) (B : Matrix (Fin d) (Fin d) ℂ)
    (hB : B.transpose = B) : MvPolynomial (Sym2 (Fin d)) ℂ →+* ℂ :=
  MvPolynomial.eval (Sym2.lift ⟨B, fun i j =>
    (congrArg (fun C : Matrix (Fin d) (Fin d) ℂ => C i j) hB).symm⟩)

theorem m1b_symmetricVariables_eval (d : ℕ) (B : Matrix (Fin d) (Fin d) ℂ)
    (hB : B.transpose = B) :
    (m1b_symmetricEvaluation d B hB).mapMatrix (m1b_symmetricVariables d) = B := by
  apply Matrix.ext
  intro i j
  change m1b_symmetricEvaluation d B hB (MvPolynomial.X (Sym2.mk i j)) = B i j
  simp only [m1b_symmetricEvaluation, MvPolynomial.eval_X, Sym2.lift_mk]

theorem m1b_symmetricVariables_det_eval (d : ℕ) (B : Matrix (Fin d) (Fin d) ℂ)
    (hB : B.transpose = B) :
    m1b_symmetricEvaluation d B hB (m1b_symmetricVariables d).det = B.det := by
  rw [RingHom.map_det, m1b_symmetricVariables_eval]

theorem m1b_symmetricVariables_det_ne_zero (d : ℕ) :
    (m1b_symmetricVariables d).det ≠ 0 := by
  intro h
  have he := m1b_symmetricVariables_det_eval d 1 Matrix.transpose_one
  rw [h, map_zero, Matrix.det_one] at he
  exact zero_ne_one he

def m1b_alternatingVariables (d : ℕ) :
    Matrix (Fin d) (Fin d) (MvPolynomial {p : Fin d × Fin d // p.1 < p.2} ℂ) :=
  fun i j => if h : i < j then MvPolynomial.X ⟨(i, j), h⟩
    else if h : j < i then -MvPolynomial.X ⟨(j, i), h⟩ else 0

theorem m1b_alternatingVariables_transpose (d : ℕ) :
    (m1b_alternatingVariables d).transpose = -m1b_alternatingVariables d := by
  apply Matrix.ext
  intro i j
  by_cases hij : i < j
  · have hji : ¬j < i := not_lt_of_ge (le_of_lt hij)
    simp only [Matrix.transpose_apply, Matrix.neg_apply, m1b_alternatingVariables,
      dite_eq_left hij, dite_eq_right hji]
  · by_cases hji : j < i
    · simp only [Matrix.transpose_apply, Matrix.neg_apply, m1b_alternatingVariables,
        dite_eq_right hij, dite_eq_left hji, neg_neg]
    · simp only [Matrix.transpose_apply, Matrix.neg_apply, m1b_alternatingVariables,
        dite_eq_right hij, dite_eq_right hji, neg_zero]

theorem m1b_alternatingVariables_diagonal (d : ℕ) (i : Fin d) :
    m1b_alternatingVariables d i i = 0 := by
  simp only [m1b_alternatingVariables, lt_self_iff_false, dite_false]

def m1b_alternatingEvaluation (d : ℕ) (B : Matrix (Fin d) (Fin d) ℂ) :
    MvPolynomial {p : Fin d × Fin d // p.1 < p.2} ℂ →+* ℂ :=
  MvPolynomial.eval (fun p => B p.val.1 p.val.2)

theorem m1b_alternatingVariables_eval (d : ℕ) (B : Matrix (Fin d) (Fin d) ℂ)
    (hB : B.transpose = -B) (hdiag : ∀ i, B i i = 0) :
    (m1b_alternatingEvaluation d B).mapMatrix (m1b_alternatingVariables d) = B := by
  apply Matrix.ext
  intro i j
  change m1b_alternatingEvaluation d B (m1b_alternatingVariables d i j) = B i j
  by_cases hij : i < j
  · simp only [m1b_alternatingVariables, dite_eq_left hij,
      m1b_alternatingEvaluation, MvPolynomial.eval_X]
  · by_cases hji : j < i
    · simp only [m1b_alternatingVariables, dite_eq_right hij, dite_eq_left hji,
        map_neg, m1b_alternatingEvaluation, MvPolynomial.eval_X]
      have h : B j i = -B i j := congrArg (fun C : Matrix (Fin d) (Fin d) ℂ => C i j) hB
      rw [h, neg_neg]
    · have he : i = j := le_antisymm (not_lt.mp hji) (not_lt.mp hij)
      subst j
      rw [m1b_alternatingVariables_diagonal, map_zero, hdiag]

theorem m1b_alternatingVariables_det_eval (d : ℕ) (B : Matrix (Fin d) (Fin d) ℂ)
    (hB : B.transpose = -B) (hdiag : ∀ i, B i i = 0) :
    m1b_alternatingEvaluation d B (m1b_alternatingVariables d).det = B.det := by
  rw [RingHom.map_det, m1b_alternatingVariables_eval d B hB hdiag]

theorem m1b_alternatingVariables_det_ne_zero (d : ℕ) (B : Matrix (Fin d) (Fin d) ℂ)
    (hunit : IsUnit B) (hB : B.transpose = -B) (hdiag : ∀ i, B i i = 0) :
    (m1b_alternatingVariables d).det ≠ 0 := by
  intro h
  have he := m1b_alternatingVariables_det_eval d B hB hdiag
  rw [h, map_zero] at he
  exact (hunit.map Matrix.detMonoidHom).ne_zero he.symm

end HodgeLean.Foundations.Program
