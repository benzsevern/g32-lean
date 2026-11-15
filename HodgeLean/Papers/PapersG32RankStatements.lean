import HodgeLean.Papers.PapersG32RankDefs

namespace HodgeLean.Papers

open Matrix
open scoped Polynomial

private def papers8_c : ℚ :=
  -4869337150302392927709794715527302500429442156335511356109310625 / 2 ^ 72

private theorem papers8_c_eq : papers8_c =
    -4869337150302392927709794715527302500429442156335511356109310625 / 2 ^ 72 := rfl

private theorem papers8_c_ne_zero : papers8_c ≠ 0 := by
  norm_num [papers8_c]

private def coeffMatrix (A : Matrix (Fin 9) (Fin 9) ℚ[X]) (k : ℕ) :
    Matrix (Fin 9) (Fin 9) ℚ := fun i j => (A i j).coeff k

private theorem coeffMatrix_mul_zero (A B : Matrix (Fin 9) (Fin 9) ℚ[X]) :
    coeffMatrix (A * B) 0 = coeffMatrix A 0 * coeffMatrix B 0 := by
  ext i j
  simp [coeffMatrix, Matrix.mul_apply, Polynomial.coeff_mul,
    Finset.Nat.antidiagonal_succ, Finset.sum_add_distrib, add_assoc]

private theorem coeffMatrix_mul_one (A B : Matrix (Fin 9) (Fin 9) ℚ[X]) :
    coeffMatrix (A * B) 1 =
      coeffMatrix A 0 * coeffMatrix B 1 + coeffMatrix A 1 * coeffMatrix B 0 := by
  ext i j
  simp [coeffMatrix, Matrix.mul_apply, Polynomial.coeff_mul,
    Finset.Nat.antidiagonal_succ, Finset.sum_add_distrib, add_assoc]

private theorem coeffMatrix_mul_two (A B : Matrix (Fin 9) (Fin 9) ℚ[X]) :
    coeffMatrix (A * B) 2 = coeffMatrix A 0 * coeffMatrix B 2 +
      coeffMatrix A 1 * coeffMatrix B 1 + coeffMatrix A 2 * coeffMatrix B 0 := by
  ext i j
  simp [coeffMatrix, Matrix.mul_apply, Polynomial.coeff_mul,
    Finset.Nat.antidiagonal_succ, Finset.sum_add_distrib, add_assoc]

private theorem coeffMatrix_mul_three (A B : Matrix (Fin 9) (Fin 9) ℚ[X]) :
    coeffMatrix (A * B) 3 = coeffMatrix A 0 * coeffMatrix B 3 +
      coeffMatrix A 1 * coeffMatrix B 2 + coeffMatrix A 2 * coeffMatrix B 1 +
      coeffMatrix A 3 * coeffMatrix B 0 := by
  ext i j
  simp [coeffMatrix, Matrix.mul_apply, Polynomial.coeff_mul,
    Finset.Nat.antidiagonal_succ, Finset.sum_add_distrib, add_assoc]

@[simp] private theorem poly_coeff_zero (C : Fin 8 → Matrix (Fin 9) (Fin 9) ℚ) :
    coeffMatrix (papers8_polyOfCoeffs C) 0 = C 0 := by
  ext i j
  simp [coeffMatrix, papers8_polyOfCoeffs, Fin.sum_univ_succ, Polynomial.coeff_monomial]

private theorem poly_coeff (C : Fin 8 → Matrix (Fin 9) (Fin 9) ℚ) (k : Fin 8) :
    coeffMatrix (papers8_polyOfCoeffs C) k = C k := by
  fin_cases k <;> ext i j <;>
    simp [coeffMatrix, papers8_polyOfCoeffs, Fin.sum_univ_succ, Polynomial.coeff_monomial]

@[simp] private theorem poly_coeff_one (C : Fin 8 → Matrix (Fin 9) (Fin 9) ℚ) :
    coeffMatrix (papers8_polyOfCoeffs C) 1 = C 1 := poly_coeff C 1
@[simp] private theorem poly_coeff_two (C : Fin 8 → Matrix (Fin 9) (Fin 9) ℚ) :
    coeffMatrix (papers8_polyOfCoeffs C) 2 = C 2 := poly_coeff C 2
@[simp] private theorem poly_coeff_three (C : Fin 8 → Matrix (Fin 9) (Fin 9) ℚ) :
    coeffMatrix (papers8_polyOfCoeffs C) 3 = C 3 := poly_coeff C 3

@[simp] private theorem A_coeff_zero :
    coeffMatrix papers8_A 0 = papers8_M0.submatrix id Fin.succ := by
  ext i j
  simp [coeffMatrix, papers8_A, papers8_Mpoly, Fin.sum_univ_succ]

private theorem A_coeff (k : Fin 13) :
    coeffMatrix papers8_A k =
      ((![papers8_M0, papers8_M1, papers8_M2, papers8_M3, papers8_M4, papers8_M5,
        papers8_M6, papers8_M7, papers8_M8, papers8_M9, papers8_M10, papers8_M11,
        papers8_M12] : Fin 13 → Matrix (Fin 9) (Fin 10) ℚ) k).submatrix id Fin.succ := by
  fin_cases k <;> ext i j <;>
    simp [coeffMatrix, papers8_A, papers8_Mpoly, Fin.sum_univ_succ]

@[simp] private theorem A_coeff_one : coeffMatrix papers8_A 1 = papers8_M1.submatrix id Fin.succ :=
  A_coeff 1
@[simp] private theorem A_coeff_two : coeffMatrix papers8_A 2 = papers8_M2.submatrix id Fin.succ :=
  A_coeff 2
@[simp] private theorem A_coeff_three : coeffMatrix papers8_A 3 = papers8_M3.submatrix id Fin.succ :=
  A_coeff 3

set_option maxHeartbeats 400000 in
/-- The generated left and right transformations have determinant one.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
theorem papers8_elimination_det_aux : papers8_P.det = 1 ∧ papers8_Q.det = 1 := by
  have hLcoeff : ∀ n : Fin 8,
      ((![papers8_L0, papers8_L1, papers8_L2, papers8_L3, papers8_L4, papers8_L5,
        papers8_L6, papers8_L7] : Fin 8 → Matrix (Fin 9) (Fin 9) ℚ) n).IsLowerTriangular := by
    intro n
    fin_cases n <;> decide +kernel
  have hLtri : papers8_L.IsLowerTriangular := by
    intro i j h
    simp [papers8_L, papers8_polyOfCoeffs, hLcoeff _ h]
  have hLdiag : ∏ i : Fin 9, papers8_L i i = 1 := by
    have hd : ∀ i : Fin 9, papers8_L i i = 1 := by
      intro i
      fin_cases i <;> ext k <;>
        simp [papers8_L, papers8_polyOfCoeffs, Fin.sum_univ_succ,
          papers8_L0, papers8_L1, papers8_L2, papers8_L3, papers8_L4, papers8_L5,
          papers8_L6, papers8_L7]
    simp [hd]
  have hR : papers8_R.det = 1 := by
    have hR1 : papers8_R1 = 0 := by decide +kernel
    have hR2 : papers8_R2 = 0 := by decide +kernel
    have hR3 : papers8_R3 = 0 := by decide +kernel
    have hR4 : papers8_R4 = 0 := by decide +kernel
    have hR5 : papers8_R5 = 0 := by decide +kernel
    have hR6 : papers8_R6 = 0 := by decide +kernel
    have hR7 : papers8_R7 = 0 := by decide +kernel
    have hRmat : papers8_R = papers8_R0.map Polynomial.C := by
      ext i j k
      by_cases hk : k < 8
      · interval_cases k <;>
          simp [papers8_R, papers8_polyOfCoeffs, Fin.sum_univ_succ,
            Polynomial.coeff_monomial, hR1, hR2, hR3, hR4,
            hR5, hR6, hR7]
      · simp [papers8_R, papers8_polyOfCoeffs, Fin.sum_univ_succ,
          Polynomial.coeff_monomial, Polynomial.coeff_C, hR1, hR2, hR3, hR4,
          hR5, hR6, hR7]
    have hR0 : papers8_R0.det = 1 := by
      let σ : Equiv.Perm (Fin 9) := Equiv.swap 4 6
      let d : Fin 9 → ℚ := fun i => if i = 4 then -1 else 1
      have hmat : papers8_R0 = Matrix.diagonal d * σ.permMatrix ℚ := by decide +kernel
      rw [hmat, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permutation]
      have hs : Equiv.Perm.sign σ = -1 := by
        apply Equiv.Perm.sign_swap
        decide
      rw [hs]
      norm_num [d]
    rw [hRmat]
    change (Polynomial.C.mapMatrix papers8_R0).det = 1
    rw [← Polynomial.C.map_det, hR0]
    simp
  have hQcoeff : ∀ n : Fin 8,
      ((![papers8_Q0, papers8_Q1, papers8_Q2, papers8_Q3, papers8_Q4, papers8_Q5,
        papers8_Q6, papers8_Q7] : Fin 8 → Matrix (Fin 9) (Fin 9) ℚ) n).IsUpperTriangular := by
    intro n
    fin_cases n <;> decide +kernel
  have hQtri : papers8_Q.IsUpperTriangular := by
    intro i j h
    simp [papers8_Q, papers8_polyOfCoeffs, hQcoeff _ h]
  have hQdiag : ∏ i : Fin 9, papers8_Q i i = 1 := by
    have hQ0 : ∀ i : Fin 9, papers8_Q0 i i = 1 := by intro i; fin_cases i <;> rfl
    have hQ1 : ∀ i : Fin 9, papers8_Q1 i i = 0 := by intro i; fin_cases i <;> rfl
    have hQ2 : ∀ i : Fin 9, papers8_Q2 i i = 0 := by intro i; fin_cases i <;> rfl
    have hQ3 : ∀ i : Fin 9, papers8_Q3 i i = 0 := by intro i; fin_cases i <;> rfl
    have hQ4 : ∀ i : Fin 9, papers8_Q4 i i = 0 := by intro i; fin_cases i <;> rfl
    have hQ5 : ∀ i : Fin 9, papers8_Q5 i i = 0 := by intro i; fin_cases i <;> rfl
    have hQ6 : ∀ i : Fin 9, papers8_Q6 i i = 0 := by intro i; fin_cases i <;> rfl
    have hQ7 : ∀ i : Fin 9, papers8_Q7 i i = 0 := by intro i; fin_cases i <;> rfl
    have hcoeff : ∀ (n : Fin 8) (i : Fin 9),
        ((![papers8_Q0, papers8_Q1, papers8_Q2, papers8_Q3, papers8_Q4, papers8_Q5,
          papers8_Q6, papers8_Q7] : Fin 8 → Matrix (Fin 9) (Fin 9) ℚ) n) i i =
          if n = 0 then 1 else 0 := by
      intro n i
      fin_cases n
      · simpa using hQ0 i
      · simpa using hQ1 i
      · simpa using hQ2 i
      · simpa using hQ3 i
      · simpa using hQ4 i
      · simpa using hQ5 i
      · simpa using hQ6 i
      · simpa using hQ7 i
    have hd : ∀ i : Fin 9, papers8_Q i i = 1 := by
      intro i
      simp [papers8_Q, papers8_polyOfCoeffs, hcoeff, Fin.sum_univ_succ]
    simp [hd]
  have hL : papers8_L.det = 1 :=
    (Matrix.det_of_isLowerTriangular papers8_L hLtri).trans hLdiag
  have hQ : papers8_Q.det = 1 :=
    (Matrix.det_of_isUpperTriangular hQtri).trans hQdiag
  constructor
  · simpa [papers8_P, Matrix.det_mul, hL, hR]
  · exact hQ

/-- Degree-zero part of the concrete truncated elimination product.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
theorem papers8_elimination_certificate_degree_zero_aux :
    ∀ i j : Fin 9,
      ((papers8_P * papers8_A * papers8_Q) i j).coeff 0 = (papers8_D i j).coeff 0 := by
  intro i j
  change coeffMatrix (papers8_P * papers8_A * papers8_Q) 0 i j = coeffMatrix papers8_D 0 i j
  have h : coeffMatrix (papers8_P * papers8_A * papers8_Q) 0 = coeffMatrix papers8_D 0 := by
    simp only [coeffMatrix_mul_zero, papers8_P]
    simp [papers8_L, papers8_R, papers8_Q, papers8_D]
    decide +kernel
  exact congrFun (congrFun h i) j

/-- Degree-one part of the concrete truncated elimination product.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
theorem papers8_elimination_certificate_degree_one_aux :
    ∀ i j : Fin 9,
      ((papers8_P * papers8_A * papers8_Q) i j).coeff 1 = (papers8_D i j).coeff 1 := by
  intro i j
  change coeffMatrix (papers8_P * papers8_A * papers8_Q) 1 i j = coeffMatrix papers8_D 1 i j
  have h : coeffMatrix (papers8_P * papers8_A * papers8_Q) 1 = coeffMatrix papers8_D 1 := by
    simp only [coeffMatrix_mul_one, coeffMatrix_mul_zero, papers8_P]
    simp [papers8_L, papers8_R, papers8_Q, papers8_D]
    decide +kernel
  exact congrFun (congrFun h i) j

/-- Degree-two part of the concrete truncated elimination product.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
theorem papers8_elimination_certificate_degree_two_aux :
    ∀ i j : Fin 9,
      ((papers8_P * papers8_A * papers8_Q) i j).coeff 2 = (papers8_D i j).coeff 2 := by
  intro i j
  change coeffMatrix (papers8_P * papers8_A * papers8_Q) 2 i j = coeffMatrix papers8_D 2 i j
  have h : coeffMatrix (papers8_P * papers8_A * papers8_Q) 2 = coeffMatrix papers8_D 2 := by
    simp only [coeffMatrix_mul_two, coeffMatrix_mul_one, coeffMatrix_mul_zero, papers8_P]
    simp [papers8_L, papers8_R, papers8_Q, papers8_D]
    decide +kernel
  exact congrFun (congrFun h i) j

/-- Degree-three part of the concrete truncated elimination product.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
theorem papers8_elimination_certificate_degree_three_aux :
    ∀ i j : Fin 9,
      ((papers8_P * papers8_A * papers8_Q) i j).coeff 3 = (papers8_D i j).coeff 3 := by
  intro i j
  change coeffMatrix (papers8_P * papers8_A * papers8_Q) 3 i j = coeffMatrix papers8_D 3 i j
  have h : coeffMatrix (papers8_P * papers8_A * papers8_Q) 3 = coeffMatrix papers8_D 3 := by
    simp only [coeffMatrix_mul_three, coeffMatrix_mul_two, coeffMatrix_mul_one,
      coeffMatrix_mul_zero, papers8_P]
    simp [papers8_L, papers8_R, papers8_Q, papers8_D]
    decide +kernel
  exact congrFun (congrFun h i) j

private theorem papers8_matrix_mul_coeff (A B : Matrix (Fin 9) (Fin 9) ℚ[X])
    (i j : Fin 9) (k : ℕ) :
    ((A * B) i j).coeff k =
      ∑ x, ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal k : Finset (ℕ × ℕ)),
        (A i x).coeff p.1 * (B x j).coeff p.2 := by
  classical
  simp [Matrix.mul_apply, Polynomial.coeff_mul]

private theorem papers8_polyOfCoeffs_coeff (C : Fin 8 → Matrix (Fin 9) (Fin 9) ℚ)
    (i j : Fin 9) (k : Fin 8) :
    (papers8_polyOfCoeffs C i j).coeff k = C k i j := by
  classical
  simp [papers8_polyOfCoeffs, Polynomial.coeff_monomial, Fin.val_eq_val]

private theorem papers8_A_coeff (i j : Fin 9) (k : Fin 8) :
    (papers8_A i j).coeff k = papers8_Acoeff k i j := by
  classical
  simp [papers8_A, papers8_Acoeff, papers8_Mpoly,
    Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
  let k13 : Fin 13 := ⟨k, by omega⟩
  rw [Finset.sum_eq_single k13]
  · fin_cases k <;> rfl
  · intro b _ hb
    simp only [ite_eq_right_iff]
    intro h
    exact (hb (Fin.ext h)).elim
  · simp

set_option maxHeartbeats 400000 in
/-- Degree-four part of the concrete truncated elimination product.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
theorem papers8_elimination_certificate_degree_four_aux :
    ∀ i j : Fin 9,
      ((papers8_P * papers8_A * papers8_Q) i j).coeff 4 = (papers8_D i j).coeff 4 := by
  simp [papers8_P, papers8_matrix_mul_coeff, papers8_L, papers8_R, papers8_Q,
    papers8_D, papers8_polyOfCoeffs, papers8_A, papers8_Mpoly,
    Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Degree-five part of the concrete truncated elimination product.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
theorem papers8_elimination_certificate_degree_five_aux :
    ∀ i j : Fin 9,
      ((papers8_P * papers8_A * papers8_Q) i j).coeff 5 = (papers8_D i j).coeff 5 := by
  simp [papers8_P, papers8_matrix_mul_coeff, papers8_L, papers8_R, papers8_Q,
    papers8_D, papers8_polyOfCoeffs, papers8_A, papers8_Mpoly,
    Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Degree-six part of the concrete truncated elimination product.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
theorem papers8_elimination_certificate_degree_six_aux :
    ∀ i j : Fin 9,
      ((papers8_P * papers8_A * papers8_Q) i j).coeff 6 = (papers8_D i j).coeff 6 := by
  simp [papers8_P, papers8_matrix_mul_coeff, papers8_L, papers8_R, papers8_Q,
    papers8_D, papers8_polyOfCoeffs, papers8_A, papers8_Mpoly,
    Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Degree-seven part of the concrete truncated elimination product.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
theorem papers8_elimination_certificate_degree_seven_aux :
    ∀ i j : Fin 9,
      ((papers8_P * papers8_A * papers8_Q) i j).coeff 7 = (papers8_D i j).coeff 7 := by
  simp [papers8_P, papers8_matrix_mul_coeff, papers8_L, papers8_R, papers8_Q,
    papers8_D, papers8_polyOfCoeffs, papers8_A, papers8_Mpoly,
    Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
  decide +kernel

/-- The concrete elimination product agrees with the diagonal data through degree seven.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
theorem papers8_elimination_certificate_aux :
    ∀ (i j : Fin 9) (k : ℕ), k ≤ 7 →
      ((papers8_P * papers8_A * papers8_Q) i j).coeff k = (papers8_D i j).coeff k := by
  intro i j k hk
  interval_cases k
  · exact papers8_elimination_certificate_degree_zero_aux i j
  · exact papers8_elimination_certificate_degree_one_aux i j
  · exact papers8_elimination_certificate_degree_two_aux i j
  · exact papers8_elimination_certificate_degree_three_aux i j
  · exact papers8_elimination_certificate_degree_four_aux i j
  · exact papers8_elimination_certificate_degree_five_aux i j
  · exact papers8_elimination_certificate_degree_six_aux i j
  · exact papers8_elimination_certificate_degree_seven_aux i j

/-- Degree-zero coefficient of the diagonal product.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
theorem papers8_diagonal_product_degree_zero_aux :
    (∏ i : Fin 9, papers8_D i i).coeff 0 = 0 := by
  norm_num [papers8_D, papers8_polyOfCoeffs, Fin.prod_univ_succ, Fin.sum_univ_succ,
    papers8_D0]

/-- Degree-one coefficient of the diagonal product.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
theorem papers8_diagonal_product_degree_one_aux :
    (∏ i : Fin 9, papers8_D i i).coeff 1 = 0 := by
  norm_num [papers8_D, papers8_polyOfCoeffs, Fin.prod_univ_succ, Fin.sum_univ_succ,
    papers8_D0, papers8_D1, Polynomial.mul_coeff_one]

/-- Degree-two coefficient of the diagonal product.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
theorem papers8_diagonal_product_degree_two_aux :
    (∏ i : Fin 9, papers8_D i i).coeff 2 = 0 := by
  norm_num [papers8_D, papers8_polyOfCoeffs, Fin.prod_univ_succ, Fin.sum_univ_succ,
    papers8_D0, papers8_D1, papers8_D2, Polynomial.coeff_mul,
    Finset.Nat.antidiagonal_succ]

/-- Degree-three coefficient of the diagonal product.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
theorem papers8_diagonal_product_degree_three_aux :
    (∏ i : Fin 9, papers8_D i i).coeff 3 = 0 := by
  norm_num [papers8_D, papers8_polyOfCoeffs, Fin.prod_univ_succ, Fin.sum_univ_succ,
    papers8_D0, papers8_D1, papers8_D2, papers8_D3, Polynomial.coeff_mul,
    Finset.Nat.antidiagonal_succ]

set_option maxHeartbeats 400000 in
/-- Degree-four coefficient of the diagonal product.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
theorem papers8_diagonal_product_degree_four_aux :
    (∏ i : Fin 9, papers8_D i i).coeff 4 = 0 := by
  norm_num [papers8_D, papers8_polyOfCoeffs, Fin.prod_univ_succ, Fin.sum_univ_succ,
    papers8_D0, papers8_D1, papers8_D2, papers8_D3, papers8_D4, Polynomial.coeff_mul,
    Polynomial.coeff_monomial, Finset.Nat.antidiagonal_succ]

set_option maxHeartbeats 400000 in
/-- Degree-five coefficient of the diagonal product.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
theorem papers8_diagonal_product_degree_five_aux :
    (∏ i : Fin 9, papers8_D i i).coeff 5 = 0 := by
  norm_num [papers8_D, papers8_polyOfCoeffs, Fin.prod_univ_succ, Fin.sum_univ_succ,
    papers8_D0, papers8_D1, papers8_D2, papers8_D3, papers8_D4, papers8_D5,
    Polynomial.coeff_mul, Polynomial.coeff_monomial, Finset.Nat.antidiagonal_succ]

set_option maxHeartbeats 400000 in
/-- Degree-six coefficient of the diagonal product.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
theorem papers8_diagonal_product_degree_six_aux :
    (∏ i : Fin 9, papers8_D i i).coeff 6 = 0 := by
  norm_num [papers8_D, papers8_polyOfCoeffs, Fin.prod_univ_succ, Fin.sum_univ_succ,
    papers8_D0, papers8_D1, papers8_D2, Polynomial.coeff_mul, Polynomial.coeff_monomial,
    Finset.Nat.antidiagonal_succ]

set_option maxHeartbeats 400000 in
/-- Degree-seven coefficient of the diagonal product.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
theorem papers8_diagonal_product_degree_seven_aux :
    (∏ i : Fin 9, papers8_D i i).coeff 7 = papers8_c := by
  let u := papers8_D 0 0 * papers8_D 1 1 * papers8_D 2 2 * papers8_D 3 3 *
    papers8_D 4 4 * papers8_D 5 5
  let w := papers8_D 6 6 * papers8_D 7 7 * papers8_D 8 8
  have hprod : (∏ i : Fin 9, papers8_D i i) = u * w := by
    norm_num [u, w, Fin.prod_univ_succ]
    ring
  have hu0 : u.coeff 0 = 0 := by
    norm_num [u, papers8_D, papers8_polyOfCoeffs, Fin.sum_univ_succ, papers8_D0]
  have hu1 : u.coeff 1 =
      567 * (-32264001 / 2000) * (-673909875 / 32516) * 567 * (-42525 / 32) *
        (193541292532181 / 132710400 : ℚ) := by
    norm_num [u, papers8_D, papers8_polyOfCoeffs, Fin.sum_univ_succ, papers8_D0,
      papers8_D1, Polynomial.mul_coeff_one, Polynomial.coeff_monomial]
  have hw : ∀ k < 6, w.coeff k = 0 := by
    intro k hk
    interval_cases k <;>
      norm_num [w, papers8_D, papers8_polyOfCoeffs, Fin.sum_univ_succ, papers8_D0,
        papers8_D1, papers8_D2, Polynomial.coeff_mul, Polynomial.coeff_monomial,
        Finset.Nat.antidiagonal_succ]
  have hw6 : w.coeff 6 =
      (349402487272248074439883453 / 88787455031723098112) *
        (5701688547867302486377688293312590251 / 48164512640249507548324167680) *
        (124071154440284640242056588524405832732790625 /
          11677058146032235492101505624704184834048 : ℚ) := by
    norm_num [w, papers8_D, papers8_polyOfCoeffs, Fin.sum_univ_succ, papers8_D0,
      papers8_D1, papers8_D2, Polynomial.coeff_mul, Polynomial.coeff_monomial,
      Finset.Nat.antidiagonal_succ]
  rw [hprod, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, hu0, hu1, hw, hw6, papers8_c]

/-- The diagonal product starts in degree seven with the printed coefficient.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
theorem papers8_diagonal_product_aux :
    (∀ k < 7, (∏ i : Fin 9, papers8_D i i).coeff k = 0) ∧
      (∏ i : Fin 9, papers8_D i i).coeff 7 = papers8_c := by
  constructor
  · intro k hk
    interval_cases k <;>
      first
      | exact papers8_diagonal_product_degree_zero_aux
      | exact papers8_diagonal_product_degree_one_aux
      | exact papers8_diagonal_product_degree_two_aux
      | exact papers8_diagonal_product_degree_three_aux
      | exact papers8_diagonal_product_degree_four_aux
      | exact papers8_diagonal_product_degree_five_aux
      | exact papers8_diagonal_product_degree_six_aux
  · exact papers8_diagonal_product_degree_seven_aux

/-- Coefficients through a fixed cutoff of a determinant depend only on the entry coefficients
through that cutoff. -/
private theorem papers8_prod_coeff_congr {R : Type*} [CommRing R] {ι : Type*}
    (s : Finset ι) (f g : ι → R[X]) (d : ℕ)
    (h : ∀ i ∈ s, ∀ k, k ≤ d → (f i).coeff k = (g i).coeff k) :
    ∀ k, k ≤ d → (∏ i ∈ s, f i).coeff k = (∏ i ∈ s, g i).coeff k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      intro k hk
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Polynomial.coeff_mul, Polynomial.coeff_mul]
      apply Finset.sum_congr rfl
      intro x hx
      have hxsum : x.1 + x.2 = k := by simpa using hx
      have hx1 : x.1 ≤ k := by omega
      have hx2 : x.2 ≤ k := by omega
      rw [h a (Finset.mem_insert_self a s) x.1 (le_trans hx1 hk),
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) x.2 (le_trans hx2 hk)]

theorem papers8_det_coeff_congr_aux {R : Type*} [CommRing R] {n : Type*} [Fintype n]
    [DecidableEq n] (A B : Matrix n n R[X]) (d : ℕ)
    (h : ∀ (i j : n) (k : ℕ), k ≤ d → (A i j).coeff k = (B i j).coeff k) :
    ∀ k : ℕ, k ≤ d → A.det.coeff k = B.det.coeff k := by
  classical
  intro k hk
  rw [Matrix.det_apply, Matrix.det_apply,
    Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Polynomial.coeff_smul, Polynomial.coeff_smul,
    papers8_prod_coeff_congr Finset.univ (fun i => A (σ i) i) (fun i => B (σ i) i) d
      (fun i _ => h (σ i) i) k hk]

/-- A unit-diagonal elimination certificate transfers a triangular determinant computation through
a coefficient cutoff. -/
theorem papers8_triangular_bridge_aux {R : Type*} [CommRing R] {n : Type*} [Fintype n]
    [DecidableEq n] [LinearOrder n] (P A Q D : Matrix n n R[X]) (d : ℕ)
    (hP : P.det = 1) (hQ : Q.det = 1)
    (hD : ∀ (i j : n), j < i → D i j = 0)
    (hcert : ∀ (i j : n) (k : ℕ), k ≤ d →
      ((P * A * Q) i j).coeff k = (D i j).coeff k) :
    ∀ k : ℕ, k ≤ d →
      A.det.coeff k = (∏ i : n, D i i).coeff k := by
  intro k hk
  have hcoeff := papers8_det_coeff_congr_aux (P * A * Q) D d hcert k hk
  rw [Matrix.det_mul, Matrix.det_mul, hP, hQ, one_mul, mul_one] at hcoeff
  rw [Matrix.det_of_isUpperTriangular hD] at hcoeff
  exact hcoeff

private theorem papers8_D_upper : papers8_D.IsUpperTriangular := by
  have hD0 : papers8_D0.IsUpperTriangular := by decide +kernel
  have hD1 : papers8_D1.IsUpperTriangular := by decide +kernel
  have hD2 : papers8_D2.IsUpperTriangular := by decide +kernel
  have hD3 : papers8_D3.IsUpperTriangular := by decide +kernel
  have hD4 : papers8_D4.IsUpperTriangular := by decide +kernel
  have hD5 : papers8_D5.IsUpperTriangular := by decide +kernel
  have hD6 : papers8_D6.IsUpperTriangular := by decide +kernel
  have hD7 : papers8_D7.IsUpperTriangular := by decide +kernel
  intro i j hij
  rw [papers8_D, papers8_polyOfCoeffs]
  apply Finset.sum_eq_zero
  intro n hn
  have hz : ((![papers8_D0, papers8_D1, papers8_D2, papers8_D3, papers8_D4,
      papers8_D5, papers8_D6, papers8_D7] : Fin 8 → Matrix (Fin 9) (Fin 9) ℚ) n) i j = 0 := by
    fin_cases n
    · exact hD0 hij
    · exact hD1 hij
    · exact hD2 hij
    · exact hD3 hij
    · exact hD4 hij
    · exact hD5 hij
    · exact hD6 hij
    · exact hD7 hij
  rw [hz, Polynomial.monomial_zero_right]

private theorem papers8_triangular_bridge_rat {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    (P A Q D : Matrix n n ℚ[X])
    (hp : P.det = 1) (hq : Q.det = 1)
    (hd : D.IsUpperTriangular)
    (hc : ∀ i j k, k ≤ 7 → ((P * A * Q) i j).coeff k = (D i j).coeff k) :
    ∀ k, k ≤ 7 → A.det.coeff k = (∏ i, D i i).coeff k := by
  exact papers8_triangular_bridge_aux P A Q D 7 hp hq (fun _ _ h => hd h) hc

private theorem papers8_A_det_coeff_eq_D (k : ℕ) (hk : k ≤ 7) :
    papers8_A.det.coeff k = (∏ i : Fin 9, papers8_D i i).coeff k := by
  exact papers8_triangular_bridge_rat papers8_P papers8_A papers8_Q papers8_D
    papers8_elimination_det_aux.1 papers8_elimination_det_aux.2
    papers8_D_upper papers8_elimination_certificate_aux k hk


private theorem papers8_minor_order_seven_c :
    (∀ k < 7, papers8_A.det.coeff k = 0) ∧ papers8_A.det.coeff 7 = papers8_c := by
  constructor
  · intro k hk
    rw [papers8_A_det_coeff_eq_D k (by omega)]
    exact papers8_diagonal_product_aux.1 k hk
  · exact (papers8_A_det_coeff_eq_D 7 (by omega)).trans papers8_diagonal_product_aux.2

/-- **The omitted-column minor starts in degree seven with the printed coefficient.**
Checks: G32 v0.16, Proposition 5.9.
Source: G32 v0.16, Proposition 5.9 and the appendix "The rank certificate". -/
theorem papers_g32_minor_order_seven_aux :
    (∀ k < 7, papers8_A.det.coeff k = 0) ∧
      papers8_A.det.coeff 7 =
        -4869337150302392927709794715527302500429442156335511356109310625 / 2 ^ 72 := by
  constructor
  · exact papers8_minor_order_seven_c.1
  · exact papers8_minor_order_seven_c.2.trans papers8_c_eq

/-- The omitted-column polynomial determinant is nonzero. -/
theorem papers_g32_minor_ne_zero_aux : papers8_A.det ≠ 0 := by
  intro h
  have hcoeff := papers_g32_minor_order_seven_aux.2
  rw [h] at hcoeff
  norm_num at hcoeff

/-- The exported polynomial matrix has full row rank over the rational-function field. -/
theorem papers_g32_rank_ratFunc_aux :
    (papers8_Mpoly.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))).rank = 9 := by
  let F := papers8_Mpoly.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))
  let A := F.submatrix id Fin.succ
  have hA : A = papers8_A.map (algebraMap (Polynomial ℚ) (RatFunc ℚ)) := by
    ext i j
    rfl
  have hdet : A.det ≠ 0 := by
    rw [hA]
    intro hz
    apply papers_g32_minor_ne_zero_aux
    apply (IsFractionRing.to_map_eq_zero_iff (R := Polynomial ℚ) (K := RatFunc ℚ)).mp
    rw [(algebraMap (Polynomial ℚ) (RatFunc ℚ)).map_det]
    exact hz
  have hminor : A.rank = 9 := by
    apply Matrix.rank_of_isUnit
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hdet
  apply Nat.le_antisymm
  · simpa [F] using Matrix.rank_le_card_height F
  · calc
      9 = A.rank := hminor.symm
      _ ≤ F.rank := Matrix.rank_submatrix_le F id Fin.succ
      _ = (papers8_Mpoly.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))).rank := rfl

private theorem papers8_powerSeries_det_coeff_congr {R : Type*} [CommRing R]
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n (PowerSeries R)) (d : ℕ)
    (h : ∀ (i j : n) (k : ℕ), k ≤ d →
      PowerSeries.coeff k (A i j) = PowerSeries.coeff k (B i j)) :
    ∀ k : ℕ, k ≤ d → PowerSeries.coeff k A.det = PowerSeries.coeff k B.det := by
  have hadd : ∀ {f g f' g' : PowerSeries R}, (∀ k ≤ d, PowerSeries.coeff k f = PowerSeries.coeff k f') →
      (∀ k ≤ d, PowerSeries.coeff k g = PowerSeries.coeff k g') →
      ∀ k ≤ d, PowerSeries.coeff k (f + g) = PowerSeries.coeff k (f' + g') := by
    intro f g f' g' hf hg k hk
    simp only [map_add]
    rw [hf k hk, hg k hk]
  have hmul : ∀ {f g f' g' : PowerSeries R}, (∀ k ≤ d, PowerSeries.coeff k f = PowerSeries.coeff k f') →
      (∀ k ≤ d, PowerSeries.coeff k g = PowerSeries.coeff k g') →
      ∀ k ≤ d, PowerSeries.coeff k (f * g) = PowerSeries.coeff k (f' * g') := by
    intro f g f' g' hf hg k hk
    simp only [PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' : p.1 + p.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [hf p.1 (by omega), hg p.2 (by omega)]
  have hprod : ∀ σ : Equiv.Perm n,
      ∀ k ≤ d, PowerSeries.coeff k (∏ i, A (σ i) i) =
        PowerSeries.coeff k (∏ i, B (σ i) i) := by
    intro σ
    induction (Finset.univ : Finset n) using Finset.induction_on with
    | empty => intro k hk; rfl
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.prod_insert hi]
        exact hmul (h (σ i) i) ih
  have hsmul : ∀ (z : ℤ) {f g : PowerSeries R}, (∀ k ≤ d, PowerSeries.coeff k f = PowerSeries.coeff k g) →
      ∀ k ≤ d, PowerSeries.coeff k (z • f) = PowerSeries.coeff k (z • g) := by
    intro z f g hf k hk
    rw [map_zsmul, map_zsmul, hf k hk]
  rw [Matrix.det_apply, Matrix.det_apply]
  have hsum : ∀ k ≤ d,
      PowerSeries.coeff k (∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, A (σ i) i) =
      PowerSeries.coeff k (∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, B (σ i) i) := by
    induction (Finset.univ : Finset (Equiv.Perm n)) using Finset.induction_on with
    | empty => intro k hk; rfl
    | @insert σ s hσ ih =>
        rw [Finset.sum_insert hσ, Finset.sum_insert hσ]
        exact hadd (hsmul _ (hprod σ)) ih
  exact hsum

private theorem papers8_det_polynomial_coe {R : Type*} [CommRing R]
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n R[X]) :
    Matrix.det ((fun i j => (A i j : PowerSeries R)) : Matrix n n (PowerSeries R)) =
      (A.det : PowerSeries R) := by
  change (Polynomial.coeToPowerSeries.ringHom.mapMatrix A).det =
    Polynomial.coeToPowerSeries.ringHom A.det
  exact (Polynomial.coeToPowerSeries.ringHom.map_det A).symm

private theorem papers8_Mseries_coeff_eq_A (i j : Fin 9) (k : ℕ) (hk : k ≤ 7) :
    PowerSeries.coeff k (papers8_Mseries i (Fin.succ j)) =
      PowerSeries.coeff k (papers8_A i j : PowerSeries ℚ) := by
  interval_cases k <;>
    simp [papers8_Mseries, papers8_A, papers8_Mpoly, Fin.sum_univ_succ,
      PowerSeries.coeff_monomial, ← PowerSeries.coeff_zero_eq_constantCoeff]

private theorem papers8_powerSeries_order_rat {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℚ[X]) (B : Matrix n n (PowerSeries ℚ))
    (hentries : ∀ i j k, k ≤ 7 →
      PowerSeries.coeff k (B i j) = PowerSeries.coeff k (A i j : PowerSeries ℚ))
    (hzero : ∀ k < 7, A.det.coeff k = 0) (hlead : A.det.coeff 7 ≠ 0) :
    PowerSeries.order B.det = 7 := by
  have hcoeff := papers8_powerSeries_det_coeff_congr B
    (fun i j => (A i j : PowerSeries ℚ)) 7 hentries
  rw [papers8_det_polynomial_coe A] at hcoeff
  apply (PowerSeries.order_eq_nat (n := 7)).mpr
  constructor
  · rw [hcoeff 7 (by omega), Polynomial.coeff_coe]
    exact hlead
  · intro k hk
    rw [hcoeff k (by omega), Polynomial.coeff_coe]
    exact hzero k hk

/-- Any rational power-series matrix with the same first eight coefficients has omitted-column
minor of order seven. -/
theorem papers_g32_powerSeries_order_aux
    (B : Matrix (Fin 9) (Fin 10) (PowerSeries ℚ))
    (hB : ∀ (i : Fin 9) (j : Fin 10) (k : ℕ), k ≤ 7 →
      PowerSeries.coeff k (B i j) = PowerSeries.coeff k (papers8_Mseries i j)) :
    PowerSeries.order (B.submatrix id Fin.succ).det = 7 := by
  apply papers8_powerSeries_order_rat papers8_A (B.submatrix id Fin.succ)
  · intro i j k hk
    exact (hB i (Fin.succ j) k hk).trans (papers8_Mseries_coeff_eq_A i j k hk)
  · exact papers8_minor_order_seven_c.1
  · rw [papers8_minor_order_seven_c.2]
    exact papers8_c_ne_zero

private theorem papers8_powerSeries_order_complex {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℚ[X]) (B : Matrix n n (PowerSeries ℂ))
    (hentries : ∀ i j k, k ≤ 7 → PowerSeries.coeff k (B i j) =
      algebraMap ℚ ℂ (PowerSeries.coeff k (A i j : PowerSeries ℚ)))
    (hzero : ∀ k < 7, A.det.coeff k = 0) (hlead : A.det.coeff 7 ≠ 0) :
    PowerSeries.order B.det = 7 := by
  let f : ℚ →+* ℂ := algebraMap ℚ ℂ
  let C : Matrix n n (PowerSeries ℂ) :=
    fun i j => PowerSeries.map f (A i j : PowerSeries ℚ)
  have hcoeff := papers8_powerSeries_det_coeff_congr B C 7 (by
    intro i j k hk
    exact (hentries i j k hk).trans (PowerSeries.coeff_map f k _).symm)
  have hCdet : C.det = PowerSeries.map f (A.det : PowerSeries ℚ) := by
    exact ((PowerSeries.map f).map_det
      (fun i j => (A i j : PowerSeries ℚ))).symm.trans
        (congrArg (PowerSeries.map f) (papers8_det_polynomial_coe A))
  apply (PowerSeries.order_eq_nat (n := 7)).mpr
  constructor
  · rw [hcoeff 7 (by omega), hCdet, PowerSeries.coeff_map, Polynomial.coeff_coe]
    exact (map_ne_zero_iff f (FaithfulSMul.algebraMap_injective ℚ ℂ)).mpr hlead
  · intro k hk
    rw [hcoeff k (by omega), hCdet, PowerSeries.coeff_map, Polynomial.coeff_coe,
      hzero k hk, map_zero]

/-- The complex scalar extension of any matching jet has omitted-column minor of order seven. -/
theorem papers_g32_powerSeries_order_complex_aux
    (B : Matrix (Fin 9) (Fin 10) (PowerSeries ℂ))
    (hB : ∀ (i : Fin 9) (j : Fin 10) (k : ℕ), k ≤ 7 →
      PowerSeries.coeff k (B i j) =
        algebraMap ℚ ℂ (PowerSeries.coeff k (papers8_Mseries i j))) :
    PowerSeries.order (B.submatrix id Fin.succ).det = 7 := by
  apply papers8_powerSeries_order_complex papers8_A (B.submatrix id Fin.succ)
  · intro i j k hk
    exact (hB i (Fin.succ j) k hk).trans
      (congrArg (algebraMap ℚ ℂ) (papers8_Mseries_coeff_eq_A i j k hk))
  · exact papers8_minor_order_seven_c.1
  · rw [papers8_minor_order_seven_c.2]
    exact papers8_c_ne_zero

end HodgeLean.Papers
