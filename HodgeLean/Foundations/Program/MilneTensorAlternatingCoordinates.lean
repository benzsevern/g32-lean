import HodgeLean.Foundations.Program.MilneTensorFormPolynomial

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [LinearOrder ι]

def m1b_alternatingCoordinateMatrix (ζ : Type*) :
    Matrix ι ι (MvPolynomial ({p : ι × ι // p.1 < p.2} ⊕ ζ) ℂ) :=
  fun i j => if h : i < j then MvPolynomial.X (Sum.inl ⟨(i, j), h⟩)
    else if h : j < i then -MvPolynomial.X (Sum.inl ⟨(j, i), h⟩) else 0

theorem m1b_alternatingCoordinateMatrix_transpose (ζ : Type*) :
    (m1b_alternatingCoordinateMatrix (ι := ι) ζ).transpose =
      -m1b_alternatingCoordinateMatrix ζ := by
  ext i j
  by_cases hij : i < j
  · have hji : ¬j < i := not_lt_of_ge (le_of_lt hij)
    simp only [Matrix.transpose_apply, Matrix.neg_apply, m1b_alternatingCoordinateMatrix,
      dite_eq_left hij, dite_eq_right hji]
  · by_cases hji : j < i
    · simp only [Matrix.transpose_apply, Matrix.neg_apply, m1b_alternatingCoordinateMatrix,
        dite_eq_right hij, dite_eq_left hji, neg_neg]
    · simp only [Matrix.transpose_apply, Matrix.neg_apply, m1b_alternatingCoordinateMatrix,
        dite_eq_right hij, dite_eq_right hji, neg_zero]

theorem m1b_alternatingCoordinateMatrix_diagonal (ζ : Type*) (i : ι) :
    m1b_alternatingCoordinateMatrix ζ i i = 0 := by
  simp only [m1b_alternatingCoordinateMatrix, lt_self_iff_false, dite_false]

theorem m1b_alternatingCoordinateMatrix_eval [Fintype ι] {ζ : Type*}
    (Q : Matrix ι ι ℂ) (hQ : ∀ i j, Q j i = -Q i j) (hdiag : ∀ i, Q i i = 0)
    (v : ζ → ℂ) :
    (MvPolynomial.eval (Sum.elim (fun p : {p : ι × ι // p.1 < p.2} => Q p.val.1 p.val.2) v)).mapMatrix
      (m1b_alternatingCoordinateMatrix ζ) = Q := by
  ext i j
  change MvPolynomial.eval
    (Sum.elim (fun p : {p : ι × ι // p.1 < p.2} => Q p.val.1 p.val.2) v)
    (m1b_alternatingCoordinateMatrix ζ i j) = Q i j
  by_cases hij : i < j
  · simp only [m1b_alternatingCoordinateMatrix, dite_eq_left hij, MvPolynomial.eval_X, Sum.elim_inl]
  · by_cases hji : j < i
    · simp only [m1b_alternatingCoordinateMatrix, dite_eq_right hij, dite_eq_left hji,
        map_neg, MvPolynomial.eval_X, Sum.elim_inl]
      rw [hQ, neg_neg]
    · have he : i = j := le_antisymm (not_lt.mp hji) (not_lt.mp hij)
      subst j
      rw [m1b_alternatingCoordinateMatrix_diagonal, map_zero, hdiag]

end HodgeLean.Foundations.Program
