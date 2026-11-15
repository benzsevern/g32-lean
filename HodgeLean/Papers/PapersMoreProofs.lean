import HodgeLean.Papers.PapersMoreDefs

/-! # Proofs for the compact paper results, batch 4

The `_aux` theorems behind the frozen spec `HodgeLean/Papers/PapersMore.lean`
(`docs/specs/PapersMore.md`). Every theorem here is still open.
-/

namespace HodgeLean.Papers

open Polynomial Matrix

/-! ## Statements 1–5: the sixteen products of `r₁, r₂, x`

Each word product is computed as an explicit matrix with entries `(aω + b)/3`, reduced with
`ω² = −ω − 1`; the coordinates of a vanishing combination are then inverted explicitly over `ℚ(ω)`. -/

private theorem g32_word_e {K : Type*} [Field K] {ω : K} :
    g32WordMat ω [] = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  rw [show g32WordMat ω [] = 1 by simp [g32WordMat]]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem g32_word_a {K : Type*} [Field K] {ω : K} :
    g32WordMat ω [0] = !![((ω + 2) / 3), ((2 * ω + 1) / 3), 0, ((-2 * ω - 1) / 3); ((-ω - 2) / 3), ((ω + 2) / 3), 0, ((-ω + 1) / 3); 0, 0, 1, 0; ((ω + 2) / 3), ((-ω + 1) / 3), 0, ((ω + 2) / 3)] := by
  rw [show g32WordMat ω [0] = g32R1 ω by simp [g32WordMat, g32Gen]]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g32R1] <;> ring

private theorem g32_word_b {K : Type*} [Field K] {ω : K} :
    g32WordMat ω [1] = !![((-ω + 1) / 3), ((2 * ω + 1) / 3), ((2 * ω + 1) / 3), 0; ((-ω + 1) / 3), ((-ω + 1) / 3), ((-ω - 2) / 3), 0; ((-ω + 1) / 3), ((-ω - 2) / 3), ((-ω + 1) / 3), 0; 0, 0, 0, 1] := by
  rw [show g32WordMat ω [1] = g32R2 ω by simp [g32WordMat, g32Gen]]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g32R2] <;> ring

private theorem g32_word_c {K : Type*} [Field K] {ω : K} :
    g32WordMat ω [2] = !![(-1), 0, 0, 0; 0, ((-ω - 2) / 3), ((-2 * ω - 1) / 3), ((-ω + 1) / 3); 0, ((ω + 2) / 3), ((-ω - 2) / 3), ((ω + 2) / 3); 0, ((-ω - 2) / 3), ((ω - 1) / 3), ((2 * ω + 1) / 3)] := by
  rw [show g32WordMat ω [2] = g32X ω by simp [g32WordMat, g32Gen]]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g32X] <;> ring

private theorem g32_word_ab {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    g32WordMat ω [0, 1] = !![((ω + 2) / 3), ((2 * ω + 1) / 3), 0, ((-2 * ω - 1) / 3); 0, ((-ω + 1) / 3), ((-2 * ω - 1) / 3), ((-ω + 1) / 3); ((-ω + 1) / 3), ((-ω - 2) / 3), ((-ω + 1) / 3), 0; ((-ω + 1) / 3), 0, ((ω - 1) / 3), ((ω + 2) / 3)] := by
  rw [show g32WordMat ω [0, 1] = g32R1 ω * g32R2 ω by simp [g32WordMat, g32Gen]]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, g32R1, g32R2] <;> grind

private theorem g32_word_ac {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    g32WordMat ω [0, 2] = !![((-ω - 2) / 3), 0, ((ω + 2) / 3), ((ω + 2) / 3); ((ω + 2) / 3), ((-ω - 2) / 3), 0, ((ω + 2) / 3); 0, ((ω + 2) / 3), ((-ω - 2) / 3), ((ω + 2) / 3); ((-ω - 2) / 3), ((-ω - 2) / 3), ((-ω - 2) / 3), 0] := by
  rw [show g32WordMat ω [0, 2] = g32R1 ω * g32X ω by simp [g32WordMat, g32Gen]]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, g32R1, g32X] <;> grind

private theorem g32_word_ba {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    g32WordMat ω [1, 0] = !![((-ω + 1) / 3), ((2 * ω + 1) / 3), ((2 * ω + 1) / 3), 0; 0, ((ω + 2) / 3), ((-ω - 2) / 3), ((-2 * ω - 1) / 3); ((ω + 2) / 3), 0, ((-ω + 1) / 3), ((-ω - 2) / 3); ((ω + 2) / 3), ((-ω + 1) / 3), 0, ((ω + 2) / 3)] := by
  rw [show g32WordMat ω [1, 0] = g32R2 ω * g32R1 ω by simp [g32WordMat, g32Gen]]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, g32R1, g32R2] <;> grind

private theorem g32_word_bc {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    g32WordMat ω [1, 2] = !![((ω - 1) / 3), 0, ((-ω + 1) / 3), ((2 * ω + 1) / 3); ((ω - 1) / 3), ((-ω - 2) / 3), 0, ((-2 * ω - 1) / 3); ((ω - 1) / 3), ((ω + 2) / 3), ((ω - 1) / 3), 0; 0, ((-ω - 2) / 3), ((ω - 1) / 3), ((2 * ω + 1) / 3)] := by
  rw [show g32WordMat ω [1, 2] = g32R2 ω * g32X ω by simp [g32WordMat, g32Gen]]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, g32R2, g32X] <;> grind

private theorem g32_word_ca {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    g32WordMat ω [2, 0] = !![((-ω - 2) / 3), ((-2 * ω - 1) / 3), 0, ((2 * ω + 1) / 3); ((ω + 2) / 3), ((-2 * ω - 1) / 3), ((-2 * ω - 1) / 3), 0; 0, ((ω + 2) / 3), ((-ω - 2) / 3), ((ω + 2) / 3); ((2 * ω + 1) / 3), 0, ((ω - 1) / 3), ((ω - 1) / 3)] := by
  rw [show g32WordMat ω [2, 0] = g32X ω * g32R1 ω by simp [g32WordMat, g32Gen]]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, g32R1, g32X] <;> grind

private theorem g32_word_cb {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    g32WordMat ω [2, 1] = !![((ω - 1) / 3), ((-2 * ω - 1) / 3), ((-2 * ω - 1) / 3), 0; ((-ω - 2) / 3), ((ω - 1) / 3), 0, ((-ω + 1) / 3); 0, ((ω + 2) / 3), ((-ω - 2) / 3), ((ω + 2) / 3); ((ω - 1) / 3), 0, ((2 * ω + 1) / 3), ((2 * ω + 1) / 3)] := by
  rw [show g32WordMat ω [2, 1] = g32X ω * g32R2 ω by simp [g32WordMat, g32Gen]]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, g32R2, g32X] <;> grind

private theorem g32_word_cc {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    g32WordMat ω [2, 2] = !![1, 0, 0, 0; 0, 0, ω, 0; 0, (-ω - 1), 0, 0; 0, 0, 0, (-1)] := by
  rw [show g32WordMat ω [2, 2] = g32X ω * g32X ω by simp [g32WordMat, g32Gen]]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, g32X] <;> grind

private theorem g32_word_abc {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    g32WordMat ω [0, 1, 2] = !![((-ω - 2) / 3), 0, ((ω + 2) / 3), ((ω + 2) / 3); 0, ((-ω - 2) / 3), ((ω - 1) / 3), ((-ω + 1) / 3); ((ω - 1) / 3), ((ω + 2) / 3), ((ω - 1) / 3), 0; ((ω - 1) / 3), ((-ω - 2) / 3), 0, ((ω - 1) / 3)] := by
  rw [show g32WordMat ω [0, 1, 2] = g32WordMat ω [0, 1] * g32X ω by simp [g32WordMat, g32Gen, mul_assoc], g32_word_ab hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, g32X] <;> grind

private theorem g32_word_bac {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    g32WordMat ω [1, 0, 2] = !![((ω - 1) / 3), 0, ((-ω + 1) / 3), ((2 * ω + 1) / 3); 0, ((-ω - 2) / 3), ((ω + 2) / 3), ((-ω + 1) / 3); ((-ω - 2) / 3), ((ω + 2) / 3), 0, ((-ω + 1) / 3); ((-ω - 2) / 3), ((-ω - 2) / 3), ((-ω - 2) / 3), 0] := by
  rw [show g32WordMat ω [1, 0, 2] = g32WordMat ω [1, 0] * g32X ω by simp [g32WordMat, g32Gen, mul_assoc], g32_word_ba hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, g32X] <;> grind

private theorem g32_word_cac {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    g32WordMat ω [2, 0, 2] = !![((ω + 2) / 3), 0, ((-ω - 2) / 3), ((-ω - 2) / 3); ((-ω - 2) / 3), 0, ((ω - 1) / 3), ((-2 * ω - 1) / 3); 0, (-ω - 1), 0, 0; ((-2 * ω - 1) / 3), 0, ((-ω + 1) / 3), ((-ω - 2) / 3)] := by
  rw [show g32WordMat ω [2, 0, 2] = g32WordMat ω [2, 0] * g32X ω by simp [g32WordMat, g32Gen, mul_assoc], g32_word_ca hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, g32X] <;> grind

private theorem g32_word_cba {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    g32WordMat ω [2, 1, 0] = !![((ω - 1) / 3), ((-2 * ω - 1) / 3), ((-2 * ω - 1) / 3), 0; ((-ω + 1) / 3), ((-2 * ω - 1) / 3), 0, ((2 * ω + 1) / 3); 0, ((ω + 2) / 3), ((-ω - 2) / 3), ((ω + 2) / 3); ((ω - 1) / 3), 0, ((2 * ω + 1) / 3), ((2 * ω + 1) / 3)] := by
  rw [show g32WordMat ω [2, 1, 0] = g32WordMat ω [2, 1] * g32R1 ω by simp [g32WordMat, g32Gen, mul_assoc], g32_word_cb hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, g32R1] <;> grind

private theorem g32_word_cbc {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    g32WordMat ω [2, 1, 2] = !![((-ω + 1) / 3), 0, ((ω - 1) / 3), ((-2 * ω - 1) / 3); ((ω + 2) / 3), 0, ((2 * ω + 1) / 3), ((2 * ω + 1) / 3); 0, (-ω - 1), 0, 0; ((-ω + 1) / 3), 0, ((-2 * ω - 1) / 3), ((ω - 1) / 3)] := by
  rw [show g32WordMat ω [2, 1, 2] = g32WordMat ω [2, 1] * g32X ω by simp [g32WordMat, g32Gen, mul_assoc], g32_word_cb hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, g32X] <;> grind

private theorem g32_word_coord_0 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K) :
    (∑ i, g i • g32WordMat ω (g32SpanWords i)) 0 0 = g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * (-1) + g 4 * ((ω + 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((ω - 1) / 3) + g 10 * 1 + g 11 * ((-ω - 2) / 3) + g 12 * ((ω - 1) / 3) + g 13 * ((ω + 2) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) := by
  simp only [Matrix.sum_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.smul_apply, smul_eq_mul, g32SpanWords,
    Matrix.cons_val_zero, Matrix.cons_val_succ, g32_word_e, g32_word_a, g32_word_b, g32_word_c, g32_word_ab hω, g32_word_ac hω, g32_word_ba hω, g32_word_bc hω, g32_word_ca hω, g32_word_cb hω, g32_word_cc hω, g32_word_abc hω, g32_word_bac hω, g32_word_cac hω, g32_word_cba hω, g32_word_cbc hω]
  simp
  ring

private theorem g32_word_coord_1 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K) :
    (∑ i, g i • g32WordMat ω (g32SpanWords i)) 0 1 = g 1 * ((2 * ω + 1) / 3) + g 2 * ((2 * ω + 1) / 3) + g 4 * ((2 * ω + 1) / 3) + g 6 * ((2 * ω + 1) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 14 * ((-2 * ω - 1) / 3) := by
  simp only [Matrix.sum_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.smul_apply, smul_eq_mul, g32SpanWords,
    Matrix.cons_val_zero, Matrix.cons_val_succ, g32_word_e, g32_word_a, g32_word_b, g32_word_c, g32_word_ab hω, g32_word_ac hω, g32_word_ba hω, g32_word_bc hω, g32_word_ca hω, g32_word_cb hω, g32_word_cc hω, g32_word_abc hω, g32_word_bac hω, g32_word_cac hω, g32_word_cba hω, g32_word_cbc hω]
  simp
  ring

private theorem g32_word_coord_2 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K) :
    (∑ i, g i • g32WordMat ω (g32SpanWords i)) 0 2 = g 2 * ((2 * ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((2 * ω + 1) / 3) + g 7 * ((-ω + 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) + g 15 * ((ω - 1) / 3) := by
  simp only [Matrix.sum_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.smul_apply, smul_eq_mul, g32SpanWords,
    Matrix.cons_val_zero, Matrix.cons_val_succ, g32_word_e, g32_word_a, g32_word_b, g32_word_c, g32_word_ab hω, g32_word_ac hω, g32_word_ba hω, g32_word_bc hω, g32_word_ca hω, g32_word_cb hω, g32_word_cc hω, g32_word_abc hω, g32_word_bac hω, g32_word_cac hω, g32_word_cba hω, g32_word_cbc hω]
  simp
  ring

private theorem g32_word_coord_3 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K) :
    (∑ i, g i • g32WordMat ω (g32SpanWords i)) 0 3 = g 1 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((2 * ω + 1) / 3) + g 8 * ((2 * ω + 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((2 * ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 15 * ((-2 * ω - 1) / 3) := by
  simp only [Matrix.sum_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.smul_apply, smul_eq_mul, g32SpanWords,
    Matrix.cons_val_zero, Matrix.cons_val_succ, g32_word_e, g32_word_a, g32_word_b, g32_word_c, g32_word_ab hω, g32_word_ac hω, g32_word_ba hω, g32_word_bc hω, g32_word_ca hω, g32_word_cb hω, g32_word_cc hω, g32_word_abc hω, g32_word_bac hω, g32_word_cac hω, g32_word_cba hω, g32_word_cbc hω]
  simp
  ring

private theorem g32_word_coord_4 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K) :
    (∑ i, g i • g32WordMat ω (g32SpanWords i)) 1 0 = g 1 * ((-ω - 2) / 3) + g 2 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((-ω - 2) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-ω + 1) / 3) + g 15 * ((ω + 2) / 3) := by
  simp only [Matrix.sum_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.smul_apply, smul_eq_mul, g32SpanWords,
    Matrix.cons_val_zero, Matrix.cons_val_succ, g32_word_e, g32_word_a, g32_word_b, g32_word_c, g32_word_ab hω, g32_word_ac hω, g32_word_ba hω, g32_word_bc hω, g32_word_ca hω, g32_word_cb hω, g32_word_cc hω, g32_word_abc hω, g32_word_bac hω, g32_word_cac hω, g32_word_cba hω, g32_word_cbc hω]
  simp
  ring

private theorem g32_word_coord_5 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K) :
    (∑ i, g i • g32WordMat ω (g32SpanWords i)) 1 1 = g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) := by
  simp only [Matrix.sum_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.smul_apply, smul_eq_mul, g32SpanWords,
    Matrix.cons_val_zero, Matrix.cons_val_succ, g32_word_e, g32_word_a, g32_word_b, g32_word_c, g32_word_ab hω, g32_word_ac hω, g32_word_ba hω, g32_word_bc hω, g32_word_ca hω, g32_word_cb hω, g32_word_cc hω, g32_word_abc hω, g32_word_bac hω, g32_word_cac hω, g32_word_cba hω, g32_word_cbc hω]
  simp
  ring

private theorem g32_word_coord_6 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K) :
    (∑ i, g i • g32WordMat ω (g32SpanWords i)) 1 2 = g 2 * ((-ω - 2) / 3) + g 3 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 10 * ω + g 11 * ((ω - 1) / 3) + g 12 * ((ω + 2) / 3) + g 13 * ((ω - 1) / 3) + g 15 * ((2 * ω + 1) / 3) := by
  simp only [Matrix.sum_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.smul_apply, smul_eq_mul, g32SpanWords,
    Matrix.cons_val_zero, Matrix.cons_val_succ, g32_word_e, g32_word_a, g32_word_b, g32_word_c, g32_word_ab hω, g32_word_ac hω, g32_word_ba hω, g32_word_bc hω, g32_word_ca hω, g32_word_cb hω, g32_word_cc hω, g32_word_abc hω, g32_word_bac hω, g32_word_cac hω, g32_word_cba hω, g32_word_cbc hω]
  simp
  ring

private theorem g32_word_coord_7 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K) :
    (∑ i, g i • g32WordMat ω (g32SpanWords i)) 1 3 = g 1 * ((-ω + 1) / 3) + g 3 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-2 * ω - 1) / 3) + g 7 * ((-2 * ω - 1) / 3) + g 9 * ((-ω + 1) / 3) + g 11 * ((-ω + 1) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((2 * ω + 1) / 3) := by
  simp only [Matrix.sum_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.smul_apply, smul_eq_mul, g32SpanWords,
    Matrix.cons_val_zero, Matrix.cons_val_succ, g32_word_e, g32_word_a, g32_word_b, g32_word_c, g32_word_ab hω, g32_word_ac hω, g32_word_ba hω, g32_word_bc hω, g32_word_ca hω, g32_word_cb hω, g32_word_cc hω, g32_word_abc hω, g32_word_bac hω, g32_word_cac hω, g32_word_cba hω, g32_word_cbc hω]
  simp
  ring

private theorem g32_word_coord_8 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K) :
    (∑ i, g i • g32WordMat ω (g32SpanWords i)) 2 0 = g 2 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) := by
  simp only [Matrix.sum_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.smul_apply, smul_eq_mul, g32SpanWords,
    Matrix.cons_val_zero, Matrix.cons_val_succ, g32_word_e, g32_word_a, g32_word_b, g32_word_c, g32_word_ab hω, g32_word_ac hω, g32_word_ba hω, g32_word_bc hω, g32_word_ca hω, g32_word_cb hω, g32_word_cc hω, g32_word_abc hω, g32_word_bac hω, g32_word_cac hω, g32_word_cba hω, g32_word_cbc hω]
  simp
  ring

private theorem g32_word_coord_9 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K) :
    (∑ i, g i • g32WordMat ω (g32SpanWords i)) 2 1 = g 2 * ((-ω - 2) / 3) + g 3 * ((ω + 2) / 3) + g 4 * ((-ω - 2) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω + 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 10 * (-ω - 1) + g 11 * ((ω + 2) / 3) + g 12 * ((ω + 2) / 3) + g 13 * (-ω - 1) + g 14 * ((ω + 2) / 3) + g 15 * (-ω - 1) := by
  simp only [Matrix.sum_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.smul_apply, smul_eq_mul, g32SpanWords,
    Matrix.cons_val_zero, Matrix.cons_val_succ, g32_word_e, g32_word_a, g32_word_b, g32_word_c, g32_word_ab hω, g32_word_ac hω, g32_word_ba hω, g32_word_bc hω, g32_word_ca hω, g32_word_cb hω, g32_word_cc hω, g32_word_abc hω, g32_word_bac hω, g32_word_cac hω, g32_word_cba hω, g32_word_cbc hω]
  simp
  ring

private theorem g32_word_coord_10 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K) :
    (∑ i, g i • g32WordMat ω (g32SpanWords i)) 2 2 = g 0 * 1 + g 1 * 1 + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((-ω - 2) / 3) + g 11 * ((ω - 1) / 3) + g 14 * ((-ω - 2) / 3) := by
  simp only [Matrix.sum_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.smul_apply, smul_eq_mul, g32SpanWords,
    Matrix.cons_val_zero, Matrix.cons_val_succ, g32_word_e, g32_word_a, g32_word_b, g32_word_c, g32_word_ab hω, g32_word_ac hω, g32_word_ba hω, g32_word_bc hω, g32_word_ca hω, g32_word_cb hω, g32_word_cc hω, g32_word_abc hω, g32_word_bac hω, g32_word_cac hω, g32_word_cba hω, g32_word_cbc hω]
  simp
  ring

private theorem g32_word_coord_11 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K) :
    (∑ i, g i • g32WordMat ω (g32SpanWords i)) 2 3 = g 3 * ((ω + 2) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 14 * ((ω + 2) / 3) := by
  simp only [Matrix.sum_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.smul_apply, smul_eq_mul, g32SpanWords,
    Matrix.cons_val_zero, Matrix.cons_val_succ, g32_word_e, g32_word_a, g32_word_b, g32_word_c, g32_word_ab hω, g32_word_ac hω, g32_word_ba hω, g32_word_bc hω, g32_word_ca hω, g32_word_cb hω, g32_word_cc hω, g32_word_abc hω, g32_word_bac hω, g32_word_cac hω, g32_word_cba hω, g32_word_cbc hω]
  simp
  ring

private theorem g32_word_coord_12 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K) :
    (∑ i, g i • g32WordMat ω (g32SpanWords i)) 3 0 = g 1 * ((ω + 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 8 * ((2 * ω + 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) := by
  simp only [Matrix.sum_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.smul_apply, smul_eq_mul, g32SpanWords,
    Matrix.cons_val_zero, Matrix.cons_val_succ, g32_word_e, g32_word_a, g32_word_b, g32_word_c, g32_word_ab hω, g32_word_ac hω, g32_word_ba hω, g32_word_bc hω, g32_word_ca hω, g32_word_cb hω, g32_word_cc hω, g32_word_abc hω, g32_word_bac hω, g32_word_cac hω, g32_word_cba hω, g32_word_cbc hω]
  simp
  ring

private theorem g32_word_coord_13 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K) :
    (∑ i, g i • g32WordMat ω (g32SpanWords i)) 3 1 = g 1 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((-ω - 2) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) := by
  simp only [Matrix.sum_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.smul_apply, smul_eq_mul, g32SpanWords,
    Matrix.cons_val_zero, Matrix.cons_val_succ, g32_word_e, g32_word_a, g32_word_b, g32_word_c, g32_word_ab hω, g32_word_ac hω, g32_word_ba hω, g32_word_bc hω, g32_word_ca hω, g32_word_cb hω, g32_word_cc hω, g32_word_abc hω, g32_word_bac hω, g32_word_cac hω, g32_word_cba hω, g32_word_cbc hω]
  simp
  ring

private theorem g32_word_coord_14 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K) :
    (∑ i, g i • g32WordMat ω (g32SpanWords i)) 3 2 = g 3 * ((ω - 1) / 3) + g 4 * ((ω - 1) / 3) + g 5 * ((-ω - 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω - 1) / 3) + g 9 * ((2 * ω + 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-ω + 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((-2 * ω - 1) / 3) := by
  simp only [Matrix.sum_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.smul_apply, smul_eq_mul, g32SpanWords,
    Matrix.cons_val_zero, Matrix.cons_val_succ, g32_word_e, g32_word_a, g32_word_b, g32_word_c, g32_word_ab hω, g32_word_ac hω, g32_word_ba hω, g32_word_bc hω, g32_word_ca hω, g32_word_cb hω, g32_word_cc hω, g32_word_abc hω, g32_word_bac hω, g32_word_cac hω, g32_word_cba hω, g32_word_cbc hω]
  simp
  ring

private theorem g32_word_coord_15 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K) :
    (∑ i, g i • g32WordMat ω (g32SpanWords i)) 3 3 = g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * 1 + g 3 * ((2 * ω + 1) / 3) + g 4 * ((ω + 2) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((2 * ω + 1) / 3) + g 8 * ((ω - 1) / 3) + g 9 * ((2 * ω + 1) / 3) + g 10 * (-1) + g 11 * ((ω - 1) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((ω - 1) / 3) := by
  simp only [Matrix.sum_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.smul_apply, smul_eq_mul, g32SpanWords,
    Matrix.cons_val_zero, Matrix.cons_val_succ, g32_word_e, g32_word_a, g32_word_b, g32_word_c, g32_word_ab hω, g32_word_ac hω, g32_word_ba hω, g32_word_bc hω, g32_word_ca hω, g32_word_cb hω, g32_word_cc hω, g32_word_abc hω, g32_word_bac hω, g32_word_cac hω, g32_word_cba hω, g32_word_cbc hω]
  simp
  ring

private theorem g32_word_solve_0 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K)
    (e0 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * (-1) + g 4 * ((ω + 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((ω - 1) / 3) + g 10 * 1 + g 11 * ((-ω - 2) / 3) + g 12 * ((ω - 1) / 3) + g 13 * ((ω + 2) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) = 0)
    (e1 : g 1 * ((2 * ω + 1) / 3) + g 2 * ((2 * ω + 1) / 3) + g 4 * ((2 * ω + 1) / 3) + g 6 * ((2 * ω + 1) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e2 : g 2 * ((2 * ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((2 * ω + 1) / 3) + g 7 * ((-ω + 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) + g 15 * ((ω - 1) / 3) = 0)
    (e4 : g 1 * ((-ω - 2) / 3) + g 2 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((-ω - 2) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-ω + 1) / 3) + g 15 * ((ω + 2) / 3) = 0)
    (e5 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e6 : g 2 * ((-ω - 2) / 3) + g 3 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 10 * ω + g 11 * ((ω - 1) / 3) + g 12 * ((ω + 2) / 3) + g 13 * ((ω - 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e9 : g 2 * ((-ω - 2) / 3) + g 3 * ((ω + 2) / 3) + g 4 * ((-ω - 2) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω + 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 10 * (-ω - 1) + g 11 * ((ω + 2) / 3) + g 12 * ((ω + 2) / 3) + g 13 * (-ω - 1) + g 14 * ((ω + 2) / 3) + g 15 * (-ω - 1) = 0)
    (e12 : g 1 * ((ω + 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 8 * ((2 * ω + 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) = 0)
    (e13 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((-ω - 2) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e14 : g 3 * ((ω - 1) / 3) + g 4 * ((ω - 1) / 3) + g 5 * ((-ω - 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω - 1) / 3) + g 9 * ((2 * ω + 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-ω + 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0) :
    g 0 = 0 := by
  linear_combination ((ω + 2) / 3) * e0 + ((ω - 1) / 3) * e1 + ((ω - 1) / 3) * e2 + ((2 * ω + 1) / 3) * e4 + ((-ω + 1) / 3) * e5 + ((-ω - 2) / 3) * e6 + (-ω) * e9 + ((ω + 2) / 3) * e12 + ((-2 * ω - 4) / 3) * e13 + ((ω - 1) / 3) * e14 - ((1/3) * g 1 + (2/3) * g 2 + (1/3) * g 3 + (1) * g 4 + (2/3) * g 6 + (1/3) * g 7 + (1/3) * g 8 + (-2/3) * g 9 + (2/3) * g 10 + (-1/3) * g 12 + (1/3) * g 13 + (-1/3) * g 14 + (2/3) * g 15) * hω

private theorem g32_word_solve_1 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K)
    (e1 : g 1 * ((2 * ω + 1) / 3) + g 2 * ((2 * ω + 1) / 3) + g 4 * ((2 * ω + 1) / 3) + g 6 * ((2 * ω + 1) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e2 : g 2 * ((2 * ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((2 * ω + 1) / 3) + g 7 * ((-ω + 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) + g 15 * ((ω - 1) / 3) = 0)
    (e3 : g 1 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((2 * ω + 1) / 3) + g 8 * ((2 * ω + 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((2 * ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0)
    (e4 : g 1 * ((-ω - 2) / 3) + g 2 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((-ω - 2) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-ω + 1) / 3) + g 15 * ((ω + 2) / 3) = 0)
    (e5 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e6 : g 2 * ((-ω - 2) / 3) + g 3 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 10 * ω + g 11 * ((ω - 1) / 3) + g 12 * ((ω + 2) / 3) + g 13 * ((ω - 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e7 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-2 * ω - 1) / 3) + g 7 * ((-2 * ω - 1) / 3) + g 9 * ((-ω + 1) / 3) + g 11 * ((-ω + 1) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e8 : g 2 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e9 : g 2 * ((-ω - 2) / 3) + g 3 * ((ω + 2) / 3) + g 4 * ((-ω - 2) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω + 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 10 * (-ω - 1) + g 11 * ((ω + 2) / 3) + g 12 * ((ω + 2) / 3) + g 13 * (-ω - 1) + g 14 * ((ω + 2) / 3) + g 15 * (-ω - 1) = 0)
    (e10 : g 0 * 1 + g 1 * 1 + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((-ω - 2) / 3) + g 11 * ((ω - 1) / 3) + g 14 * ((-ω - 2) / 3) = 0)
    (e11 : g 3 * ((ω + 2) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 14 * ((ω + 2) / 3) = 0)
    (e12 : g 1 * ((ω + 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 8 * ((2 * ω + 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) = 0)
    (e13 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((-ω - 2) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e14 : g 3 * ((ω - 1) / 3) + g 4 * ((ω - 1) / 3) + g 5 * ((-ω - 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω - 1) / 3) + g 9 * ((2 * ω + 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-ω + 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0) :
    g 1 = 0 := by
  linear_combination ((-2 * ω + 2) / 3) * e1 + ((-4 * ω - 2) / 3) * e2 + ((ω + 2) / 3) * e3 + ((ω - 1) / 3) * e4 + ((2 * ω + 1) / 3) * e5 + 1 * e6 + ((ω - 1) / 3) * e7 + ((-ω - 2) / 3) * e8 + (ω + 1) * e9 + ((-2 * ω - 1) / 3) * e10 + ((-2 * ω + 2) / 3) * e11 + ((ω - 1) / 3) * e12 + ((ω + 5) / 3) * e13 + ((-2 * ω - 1) / 3) * e14 - ((-2/3) * g 1 + (-5/3) * g 2 + (-1/3) * g 3 + (-4/3) * g 4 + (-1) * g 6 + (2/3) * g 8 + (4/3) * g 9 + (-1) * g 10 + (-2/3) * g 11 + (1) * g 12 + (-1) * g 13 + (1) * g 14 + (-1) * g 15) * hω

private theorem g32_word_solve_2 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K)
    (e0 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * (-1) + g 4 * ((ω + 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((ω - 1) / 3) + g 10 * 1 + g 11 * ((-ω - 2) / 3) + g 12 * ((ω - 1) / 3) + g 13 * ((ω + 2) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) = 0)
    (e2 : g 2 * ((2 * ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((2 * ω + 1) / 3) + g 7 * ((-ω + 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) + g 15 * ((ω - 1) / 3) = 0)
    (e3 : g 1 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((2 * ω + 1) / 3) + g 8 * ((2 * ω + 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((2 * ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0)
    (e4 : g 1 * ((-ω - 2) / 3) + g 2 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((-ω - 2) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-ω + 1) / 3) + g 15 * ((ω + 2) / 3) = 0)
    (e5 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e6 : g 2 * ((-ω - 2) / 3) + g 3 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 10 * ω + g 11 * ((ω - 1) / 3) + g 12 * ((ω + 2) / 3) + g 13 * ((ω - 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e7 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-2 * ω - 1) / 3) + g 7 * ((-2 * ω - 1) / 3) + g 9 * ((-ω + 1) / 3) + g 11 * ((-ω + 1) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e8 : g 2 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e9 : g 2 * ((-ω - 2) / 3) + g 3 * ((ω + 2) / 3) + g 4 * ((-ω - 2) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω + 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 10 * (-ω - 1) + g 11 * ((ω + 2) / 3) + g 12 * ((ω + 2) / 3) + g 13 * (-ω - 1) + g 14 * ((ω + 2) / 3) + g 15 * (-ω - 1) = 0)
    (e10 : g 0 * 1 + g 1 * 1 + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((-ω - 2) / 3) + g 11 * ((ω - 1) / 3) + g 14 * ((-ω - 2) / 3) = 0)
    (e12 : g 1 * ((ω + 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 8 * ((2 * ω + 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) = 0)
    (e13 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((-ω - 2) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e14 : g 3 * ((ω - 1) / 3) + g 4 * ((ω - 1) / 3) + g 5 * ((-ω - 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω - 1) / 3) + g 9 * ((2 * ω + 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-ω + 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0)
    (e15 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * 1 + g 3 * ((2 * ω + 1) / 3) + g 4 * ((ω + 2) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((2 * ω + 1) / 3) + g 8 * ((ω - 1) / 3) + g 9 * ((2 * ω + 1) / 3) + g 10 * (-1) + g 11 * ((ω - 1) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((ω - 1) / 3) = 0) :
    g 2 = 0 := by
  linear_combination ((ω - 1) / 3) * e0 + ((2 * ω + 4) / 3) * e2 + ((-ω - 2) / 3) * e3 + ((-2 * ω - 1) / 3) * e4 + ((-ω - 2) / 3) * e5 + ω * e6 + ((-2 * ω - 1) / 3) * e7 + ((ω - 1) / 3) * e8 + ((4 * ω - 1) / 3) * e9 + ((ω + 2) / 3) * e10 + (-ω - 1) * e12 + ((2 * ω + 1) / 3) * e13 + ((ω + 2) / 3) * e14 + ((-ω + 1) / 3) * e15 - ((-1/3) * g 2 + (-1/3) * g 3 + (-1/3) * g 4 + (-1/3) * g 6 + (1/3) * g 7 + (-4/3) * g 8 + (-1/3) * g 10 + (2/3) * g 11 + (2/3) * g 12 + (1/3) * g 13 + (-1/3) * g 14 + (-1) * g 15) * hω

private theorem g32_word_solve_3 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K)
    (e1 : g 1 * ((2 * ω + 1) / 3) + g 2 * ((2 * ω + 1) / 3) + g 4 * ((2 * ω + 1) / 3) + g 6 * ((2 * ω + 1) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e2 : g 2 * ((2 * ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((2 * ω + 1) / 3) + g 7 * ((-ω + 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) + g 15 * ((ω - 1) / 3) = 0)
    (e3 : g 1 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((2 * ω + 1) / 3) + g 8 * ((2 * ω + 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((2 * ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0)
    (e4 : g 1 * ((-ω - 2) / 3) + g 2 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((-ω - 2) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-ω + 1) / 3) + g 15 * ((ω + 2) / 3) = 0)
    (e5 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e6 : g 2 * ((-ω - 2) / 3) + g 3 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 10 * ω + g 11 * ((ω - 1) / 3) + g 12 * ((ω + 2) / 3) + g 13 * ((ω - 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e9 : g 2 * ((-ω - 2) / 3) + g 3 * ((ω + 2) / 3) + g 4 * ((-ω - 2) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω + 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 10 * (-ω - 1) + g 11 * ((ω + 2) / 3) + g 12 * ((ω + 2) / 3) + g 13 * (-ω - 1) + g 14 * ((ω + 2) / 3) + g 15 * (-ω - 1) = 0)
    (e10 : g 0 * 1 + g 1 * 1 + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((-ω - 2) / 3) + g 11 * ((ω - 1) / 3) + g 14 * ((-ω - 2) / 3) = 0)
    (e11 : g 3 * ((ω + 2) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 14 * ((ω + 2) / 3) = 0)
    (e12 : g 1 * ((ω + 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 8 * ((2 * ω + 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) = 0)
    (e13 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((-ω - 2) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e14 : g 3 * ((ω - 1) / 3) + g 4 * ((ω - 1) / 3) + g 5 * ((-ω - 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω - 1) / 3) + g 9 * ((2 * ω + 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-ω + 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0)
    (e15 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * 1 + g 3 * ((2 * ω + 1) / 3) + g 4 * ((ω + 2) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((2 * ω + 1) / 3) + g 8 * ((ω - 1) / 3) + g 9 * ((2 * ω + 1) / 3) + g 10 * (-1) + g 11 * ((ω - 1) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((ω - 1) / 3) = 0) :
    g 3 = 0 := by
  linear_combination ((-4 * ω - 5) / 3) * e1 + ((ω - 4) / 3) * e2 + ((-ω - 2) / 3) * e3 + (ω + 1) * e4 + (-ω) * e5 + (-ω - 1) * e6 + ((-5 * ω - 1) / 3) * e9 + ((2 * ω + 1) / 3) * e10 + ((-2 * ω - 1) / 3) * e11 + 1 * e12 + ((-2 * ω - 7) / 3) * e13 + ((-ω - 2) / 3) * e14 + ((ω - 1) / 3) * e15 - ((-1) * g 1 + (1/3) * g 3 + (2/3) * g 4 + (-1/3) * g 6 + (1/3) * g 7 + (4/3) * g 8 + (-1) * g 9 + (2/3) * g 10 + (-1/3) * g 12 + (1) * g 13 + (2) * g 15) * hω

private theorem g32_word_solve_4 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K)
    (e0 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * (-1) + g 4 * ((ω + 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((ω - 1) / 3) + g 10 * 1 + g 11 * ((-ω - 2) / 3) + g 12 * ((ω - 1) / 3) + g 13 * ((ω + 2) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) = 0)
    (e1 : g 1 * ((2 * ω + 1) / 3) + g 2 * ((2 * ω + 1) / 3) + g 4 * ((2 * ω + 1) / 3) + g 6 * ((2 * ω + 1) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e3 : g 1 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((2 * ω + 1) / 3) + g 8 * ((2 * ω + 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((2 * ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0)
    (e4 : g 1 * ((-ω - 2) / 3) + g 2 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((-ω - 2) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-ω + 1) / 3) + g 15 * ((ω + 2) / 3) = 0)
    (e5 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e7 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-2 * ω - 1) / 3) + g 7 * ((-2 * ω - 1) / 3) + g 9 * ((-ω + 1) / 3) + g 11 * ((-ω + 1) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e8 : g 2 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e9 : g 2 * ((-ω - 2) / 3) + g 3 * ((ω + 2) / 3) + g 4 * ((-ω - 2) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω + 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 10 * (-ω - 1) + g 11 * ((ω + 2) / 3) + g 12 * ((ω + 2) / 3) + g 13 * (-ω - 1) + g 14 * ((ω + 2) / 3) + g 15 * (-ω - 1) = 0)
    (e11 : g 3 * ((ω + 2) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 14 * ((ω + 2) / 3) = 0) :
    g 4 = 0 := by
  linear_combination ((-2 * ω - 1) / 3) * e0 + ((2 * ω + 1) / 3) * e1 + ((ω + 2) / 3) * e3 + ((-2 * ω - 1) / 3) * e4 + ((2 * ω + 1) / 3) * e5 + ((ω + 2) / 3) * e7 + ((ω + 2) / 3) * e8 + ((-ω - 2) / 3) * e9 + ((ω - 1) / 3) * e11 - ((1/3) * g 1 + (2/3) * g 2 + (-1/3) * g 3 + (-1/3) * g 4 + (2/3) * g 6 + (-2/3) * g 7 + (-2/3) * g 8 + (-1/3) * g 9 + (1/3) * g 10 + (-2/3) * g 12 + (-2/3) * g 14 + (1/3) * g 15) * hω

private theorem g32_word_solve_5 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K)
    (e0 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * (-1) + g 4 * ((ω + 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((ω - 1) / 3) + g 10 * 1 + g 11 * ((-ω - 2) / 3) + g 12 * ((ω - 1) / 3) + g 13 * ((ω + 2) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) = 0)
    (e1 : g 1 * ((2 * ω + 1) / 3) + g 2 * ((2 * ω + 1) / 3) + g 4 * ((2 * ω + 1) / 3) + g 6 * ((2 * ω + 1) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e2 : g 2 * ((2 * ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((2 * ω + 1) / 3) + g 7 * ((-ω + 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) + g 15 * ((ω - 1) / 3) = 0)
    (e3 : g 1 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((2 * ω + 1) / 3) + g 8 * ((2 * ω + 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((2 * ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0)
    (e4 : g 1 * ((-ω - 2) / 3) + g 2 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((-ω - 2) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-ω + 1) / 3) + g 15 * ((ω + 2) / 3) = 0)
    (e6 : g 2 * ((-ω - 2) / 3) + g 3 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 10 * ω + g 11 * ((ω - 1) / 3) + g 12 * ((ω + 2) / 3) + g 13 * ((ω - 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e7 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-2 * ω - 1) / 3) + g 7 * ((-2 * ω - 1) / 3) + g 9 * ((-ω + 1) / 3) + g 11 * ((-ω + 1) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e8 : g 2 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e9 : g 2 * ((-ω - 2) / 3) + g 3 * ((ω + 2) / 3) + g 4 * ((-ω - 2) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω + 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 10 * (-ω - 1) + g 11 * ((ω + 2) / 3) + g 12 * ((ω + 2) / 3) + g 13 * (-ω - 1) + g 14 * ((ω + 2) / 3) + g 15 * (-ω - 1) = 0)
    (e10 : g 0 * 1 + g 1 * 1 + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((-ω - 2) / 3) + g 11 * ((ω - 1) / 3) + g 14 * ((-ω - 2) / 3) = 0)
    (e11 : g 3 * ((ω + 2) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 14 * ((ω + 2) / 3) = 0)
    (e12 : g 1 * ((ω + 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 8 * ((2 * ω + 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) = 0)
    (e13 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((-ω - 2) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e14 : g 3 * ((ω - 1) / 3) + g 4 * ((ω - 1) / 3) + g 5 * ((-ω - 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω - 1) / 3) + g 9 * ((2 * ω + 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-ω + 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0) :
    g 5 = 0 := by
  linear_combination 1 * e0 + ((-2 * ω - 1) / 3) * e1 + ((-ω + 1) / 3) * e2 + ((ω + 2) / 3) * e3 + ((2 * ω + 1) / 3) * e4 + ((ω + 2) / 3) * e6 + ((ω - 1) / 3) * e7 + ((-2 * ω - 1) / 3) * e8 + ((-ω + 1) / 3) * e9 + (-1) * e10 + ((-2 * ω + 2) / 3) * e11 + ((2 * ω + 1) / 3) * e12 + ((-ω + 1) / 3) * e13 + ((2 * ω + 1) / 3) * e14 - ((-2/3) * g 1 + (-2/3) * g 2 + (-1/3) * g 3 + (-2/3) * g 4 + (-1/3) * g 5 + (-2/3) * g 6 + (1/3) * g 7 + (1) * g 8 + (2/3) * g 9 + (2/3) * g 10 + (1/3) * g 12 + (-2/3) * g 13 + (1) * g 14) * hω

private theorem g32_word_solve_6 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K)
    (e1 : g 1 * ((2 * ω + 1) / 3) + g 2 * ((2 * ω + 1) / 3) + g 4 * ((2 * ω + 1) / 3) + g 6 * ((2 * ω + 1) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e2 : g 2 * ((2 * ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((2 * ω + 1) / 3) + g 7 * ((-ω + 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) + g 15 * ((ω - 1) / 3) = 0)
    (e3 : g 1 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((2 * ω + 1) / 3) + g 8 * ((2 * ω + 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((2 * ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0)
    (e4 : g 1 * ((-ω - 2) / 3) + g 2 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((-ω - 2) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-ω + 1) / 3) + g 15 * ((ω + 2) / 3) = 0)
    (e5 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e6 : g 2 * ((-ω - 2) / 3) + g 3 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 10 * ω + g 11 * ((ω - 1) / 3) + g 12 * ((ω + 2) / 3) + g 13 * ((ω - 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e7 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-2 * ω - 1) / 3) + g 7 * ((-2 * ω - 1) / 3) + g 9 * ((-ω + 1) / 3) + g 11 * ((-ω + 1) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e8 : g 2 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e9 : g 2 * ((-ω - 2) / 3) + g 3 * ((ω + 2) / 3) + g 4 * ((-ω - 2) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω + 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 10 * (-ω - 1) + g 11 * ((ω + 2) / 3) + g 12 * ((ω + 2) / 3) + g 13 * (-ω - 1) + g 14 * ((ω + 2) / 3) + g 15 * (-ω - 1) = 0)
    (e10 : g 0 * 1 + g 1 * 1 + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((-ω - 2) / 3) + g 11 * ((ω - 1) / 3) + g 14 * ((-ω - 2) / 3) = 0)
    (e11 : g 3 * ((ω + 2) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 14 * ((ω + 2) / 3) = 0)
    (e12 : g 1 * ((ω + 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 8 * ((2 * ω + 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) = 0)
    (e13 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((-ω - 2) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e14 : g 3 * ((ω - 1) / 3) + g 4 * ((ω - 1) / 3) + g 5 * ((-ω - 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω - 1) / 3) + g 9 * ((2 * ω + 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-ω + 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0) :
    g 6 = 0 := by
  linear_combination ((-2 * ω - 1) / 3) * e1 + ((2 * ω - 2) / 3) * e2 + ((-2 * ω - 1) / 3) * e3 + ((ω + 2) / 3) * e4 + ((-ω + 1) / 3) * e5 + (-ω - 1) * e6 + ((ω + 2) / 3) * e7 + ((-ω + 1) / 3) * e8 + (-ω) * e9 + ((ω - 1) / 3) * e10 + ((ω - 1) / 3) * e11 + ((ω + 2) / 3) * e12 + ((-2 * ω - 1) / 3) * e13 + ((ω - 1) / 3) * e14 - ((2/3) * g 2 + (2/3) * g 3 + (1) * g 4 + (-2/3) * g 7 + (1) * g 8 + (-1/3) * g 9 + (-1/3) * g 11 + (-4/3) * g 12 + (1/3) * g 14 + (1) * g 15) * hω

private theorem g32_word_solve_7 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K)
    (e0 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * (-1) + g 4 * ((ω + 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((ω - 1) / 3) + g 10 * 1 + g 11 * ((-ω - 2) / 3) + g 12 * ((ω - 1) / 3) + g 13 * ((ω + 2) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) = 0)
    (e1 : g 1 * ((2 * ω + 1) / 3) + g 2 * ((2 * ω + 1) / 3) + g 4 * ((2 * ω + 1) / 3) + g 6 * ((2 * ω + 1) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e2 : g 2 * ((2 * ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((2 * ω + 1) / 3) + g 7 * ((-ω + 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) + g 15 * ((ω - 1) / 3) = 0)
    (e3 : g 1 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((2 * ω + 1) / 3) + g 8 * ((2 * ω + 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((2 * ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0)
    (e4 : g 1 * ((-ω - 2) / 3) + g 2 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((-ω - 2) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-ω + 1) / 3) + g 15 * ((ω + 2) / 3) = 0)
    (e6 : g 2 * ((-ω - 2) / 3) + g 3 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 10 * ω + g 11 * ((ω - 1) / 3) + g 12 * ((ω + 2) / 3) + g 13 * ((ω - 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e7 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-2 * ω - 1) / 3) + g 7 * ((-2 * ω - 1) / 3) + g 9 * ((-ω + 1) / 3) + g 11 * ((-ω + 1) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e8 : g 2 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e9 : g 2 * ((-ω - 2) / 3) + g 3 * ((ω + 2) / 3) + g 4 * ((-ω - 2) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω + 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 10 * (-ω - 1) + g 11 * ((ω + 2) / 3) + g 12 * ((ω + 2) / 3) + g 13 * (-ω - 1) + g 14 * ((ω + 2) / 3) + g 15 * (-ω - 1) = 0)
    (e10 : g 0 * 1 + g 1 * 1 + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((-ω - 2) / 3) + g 11 * ((ω - 1) / 3) + g 14 * ((-ω - 2) / 3) = 0)
    (e13 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((-ω - 2) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e14 : g 3 * ((ω - 1) / 3) + g 4 * ((ω - 1) / 3) + g 5 * ((-ω - 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω - 1) / 3) + g 9 * ((2 * ω + 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-ω + 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0)
    (e15 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * 1 + g 3 * ((2 * ω + 1) / 3) + g 4 * ((ω + 2) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((2 * ω + 1) / 3) + g 8 * ((ω - 1) / 3) + g 9 * ((2 * ω + 1) / 3) + g 10 * (-1) + g 11 * ((ω - 1) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((ω - 1) / 3) = 0) :
    g 7 = 0 := by
  linear_combination ((2 * ω + 1) / 3) * e0 + ((-2 * ω - 1) / 3) * e1 + (ω + 1) * e2 + ((-ω - 2) / 3) * e3 + ((-ω - 2) / 3) * e4 + ((ω - 1) / 3) * e6 + ((-2 * ω - 1) / 3) * e7 + ((-ω - 2) / 3) * e8 + ((2 * ω + 1) / 3) * e9 + ((-ω - 2) / 3) * e10 + ((-ω + 1) / 3) * e13 + ((ω - 1) / 3) * e14 + ((-ω + 1) / 3) * e15 - ((1/3) * g 1 + (1/3) * g 3 + (1/3) * g 6 + (2/3) * g 9 + (-1/3) * g 10 + (1/3) * g 11 + (1/3) * g 12 + (-1) * g 15) * hω

private theorem g32_word_solve_8 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K)
    (e1 : g 1 * ((2 * ω + 1) / 3) + g 2 * ((2 * ω + 1) / 3) + g 4 * ((2 * ω + 1) / 3) + g 6 * ((2 * ω + 1) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e2 : g 2 * ((2 * ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((2 * ω + 1) / 3) + g 7 * ((-ω + 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) + g 15 * ((ω - 1) / 3) = 0)
    (e3 : g 1 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((2 * ω + 1) / 3) + g 8 * ((2 * ω + 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((2 * ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0)
    (e5 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e6 : g 2 * ((-ω - 2) / 3) + g 3 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 10 * ω + g 11 * ((ω - 1) / 3) + g 12 * ((ω + 2) / 3) + g 13 * ((ω - 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e7 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-2 * ω - 1) / 3) + g 7 * ((-2 * ω - 1) / 3) + g 9 * ((-ω + 1) / 3) + g 11 * ((-ω + 1) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e9 : g 2 * ((-ω - 2) / 3) + g 3 * ((ω + 2) / 3) + g 4 * ((-ω - 2) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω + 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 10 * (-ω - 1) + g 11 * ((ω + 2) / 3) + g 12 * ((ω + 2) / 3) + g 13 * (-ω - 1) + g 14 * ((ω + 2) / 3) + g 15 * (-ω - 1) = 0)
    (e10 : g 0 * 1 + g 1 * 1 + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((-ω - 2) / 3) + g 11 * ((ω - 1) / 3) + g 14 * ((-ω - 2) / 3) = 0)
    (e11 : g 3 * ((ω + 2) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 14 * ((ω + 2) / 3) = 0)
    (e13 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((-ω - 2) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) = 0) :
    g 8 = 0 := by
  linear_combination ((2 * ω + 4) / 3) * e1 + ((-2 * ω - 1) / 3) * e2 + ((-ω + 1) / 3) * e3 + ((2 * ω + 1) / 3) * e5 + ((ω + 2) / 3) * e6 + ((2 * ω + 1) / 3) * e7 + ((2 * ω + 1) / 3) * e9 + ((-2 * ω - 1) / 3) * e10 + ((-ω + 1) / 3) * e11 + 1 * e13 - ((2/3) * g 1 + (-1/3) * g 2 + (-1/3) * g 3 + (-2/3) * g 7 + (-1) * g 8 + (1/3) * g 9 + (-1/3) * g 10 + (-2/3) * g 11 + (-2/3) * g 13 + (1/3) * g 14) * hω

private theorem g32_word_solve_9 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K)
    (e0 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * (-1) + g 4 * ((ω + 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((ω - 1) / 3) + g 10 * 1 + g 11 * ((-ω - 2) / 3) + g 12 * ((ω - 1) / 3) + g 13 * ((ω + 2) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) = 0)
    (e1 : g 1 * ((2 * ω + 1) / 3) + g 2 * ((2 * ω + 1) / 3) + g 4 * ((2 * ω + 1) / 3) + g 6 * ((2 * ω + 1) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e2 : g 2 * ((2 * ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((2 * ω + 1) / 3) + g 7 * ((-ω + 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) + g 15 * ((ω - 1) / 3) = 0)
    (e4 : g 1 * ((-ω - 2) / 3) + g 2 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((-ω - 2) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-ω + 1) / 3) + g 15 * ((ω + 2) / 3) = 0)
    (e5 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e6 : g 2 * ((-ω - 2) / 3) + g 3 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 10 * ω + g 11 * ((ω - 1) / 3) + g 12 * ((ω + 2) / 3) + g 13 * ((ω - 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e7 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-2 * ω - 1) / 3) + g 7 * ((-2 * ω - 1) / 3) + g 9 * ((-ω + 1) / 3) + g 11 * ((-ω + 1) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e8 : g 2 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e9 : g 2 * ((-ω - 2) / 3) + g 3 * ((ω + 2) / 3) + g 4 * ((-ω - 2) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω + 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 10 * (-ω - 1) + g 11 * ((ω + 2) / 3) + g 12 * ((ω + 2) / 3) + g 13 * (-ω - 1) + g 14 * ((ω + 2) / 3) + g 15 * (-ω - 1) = 0)
    (e10 : g 0 * 1 + g 1 * 1 + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((-ω - 2) / 3) + g 11 * ((ω - 1) / 3) + g 14 * ((-ω - 2) / 3) = 0)
    (e11 : g 3 * ((ω + 2) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 14 * ((ω + 2) / 3) = 0)
    (e12 : g 1 * ((ω + 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 8 * ((2 * ω + 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) = 0)
    (e13 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((-ω - 2) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e15 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * 1 + g 3 * ((2 * ω + 1) / 3) + g 4 * ((ω + 2) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((2 * ω + 1) / 3) + g 8 * ((ω - 1) / 3) + g 9 * ((2 * ω + 1) / 3) + g 10 * (-1) + g 11 * ((ω - 1) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((ω - 1) / 3) = 0) :
    g 9 = 0 := by
  linear_combination ((ω - 1) / 3) * e0 + ((4 * ω + 2) / 3) * e1 + ((ω + 2) / 3) * e2 + (-ω - 1) * e4 + ((-ω - 2) / 3) * e5 + ((ω - 1) / 3) * e6 + ((-ω + 1) / 3) * e7 + ((2 * ω + 1) / 3) * e8 + ω * e9 + ((ω + 2) / 3) * e10 + ((ω - 1) / 3) * e11 + ((-ω - 2) / 3) * e12 + ((ω + 2) / 3) * e13 + ((-ω + 1) / 3) * e15 - ((1) * g 1 + (2/3) * g 2 + (1/3) * g 4 + (2/3) * g 6 + (1/3) * g 7 + (-4/3) * g 8 + (-2/3) * g 9 + (-2/3) * g 10 + (2/3) * g 11 + (1/3) * g 12 + (-2/3) * g 14 + (-4/3) * g 15) * hω

private theorem g32_word_solve_10 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K)
    (e0 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * (-1) + g 4 * ((ω + 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((ω - 1) / 3) + g 10 * 1 + g 11 * ((-ω - 2) / 3) + g 12 * ((ω - 1) / 3) + g 13 * ((ω + 2) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) = 0)
    (e1 : g 1 * ((2 * ω + 1) / 3) + g 2 * ((2 * ω + 1) / 3) + g 4 * ((2 * ω + 1) / 3) + g 6 * ((2 * ω + 1) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e3 : g 1 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((2 * ω + 1) / 3) + g 8 * ((2 * ω + 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((2 * ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0)
    (e4 : g 1 * ((-ω - 2) / 3) + g 2 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((-ω - 2) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-ω + 1) / 3) + g 15 * ((ω + 2) / 3) = 0)
    (e5 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e6 : g 2 * ((-ω - 2) / 3) + g 3 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 10 * ω + g 11 * ((ω - 1) / 3) + g 12 * ((ω + 2) / 3) + g 13 * ((ω - 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e9 : g 2 * ((-ω - 2) / 3) + g 3 * ((ω + 2) / 3) + g 4 * ((-ω - 2) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω + 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 10 * (-ω - 1) + g 11 * ((ω + 2) / 3) + g 12 * ((ω + 2) / 3) + g 13 * (-ω - 1) + g 14 * ((ω + 2) / 3) + g 15 * (-ω - 1) = 0)
    (e10 : g 0 * 1 + g 1 * 1 + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((-ω - 2) / 3) + g 11 * ((ω - 1) / 3) + g 14 * ((-ω - 2) / 3) = 0)
    (e11 : g 3 * ((ω + 2) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 14 * ((ω + 2) / 3) = 0)
    (e12 : g 1 * ((ω + 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 8 * ((2 * ω + 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) = 0)
    (e13 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((-ω - 2) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e14 : g 3 * ((ω - 1) / 3) + g 4 * ((ω - 1) / 3) + g 5 * ((-ω - 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω - 1) / 3) + g 9 * ((2 * ω + 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-ω + 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0)
    (e15 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * 1 + g 3 * ((2 * ω + 1) / 3) + g 4 * ((ω + 2) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((2 * ω + 1) / 3) + g 8 * ((ω - 1) / 3) + g 9 * ((2 * ω + 1) / 3) + g 10 * (-1) + g 11 * ((ω - 1) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((ω - 1) / 3) = 0) :
    g 10 = 0 := by
  linear_combination ((-ω + 1) / 3) * e0 + ((-2 * ω - 4) / 3) * e1 + ((-ω - 2) / 3) * e3 + ((ω + 2) / 3) * e4 + ((-2 * ω - 1) / 3) * e5 + ((-2 * ω - 1) / 3) * e6 + ((-2 * ω - 1) / 3) * e9 + ((2 * ω + 1) / 3) * e10 + ((-2 * ω - 1) / 3) * e11 + ((-ω + 1) / 3) * e12 + (-1) * e13 + ((-2 * ω - 1) / 3) * e14 + ((ω - 1) / 3) * e15 - ((-2/3) * g 1 + (1/3) * g 4 + (-1/3) * g 6 + (1/3) * g 8 + (-1) * g 9 + (2/3) * g 13 + (-1/3) * g 14 + (4/3) * g 15) * hω

private theorem g32_word_solve_11 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K)
    (e0 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * (-1) + g 4 * ((ω + 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((ω - 1) / 3) + g 10 * 1 + g 11 * ((-ω - 2) / 3) + g 12 * ((ω - 1) / 3) + g 13 * ((ω + 2) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) = 0)
    (e1 : g 1 * ((2 * ω + 1) / 3) + g 2 * ((2 * ω + 1) / 3) + g 4 * ((2 * ω + 1) / 3) + g 6 * ((2 * ω + 1) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e2 : g 2 * ((2 * ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((2 * ω + 1) / 3) + g 7 * ((-ω + 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) + g 15 * ((ω - 1) / 3) = 0)
    (e3 : g 1 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((2 * ω + 1) / 3) + g 8 * ((2 * ω + 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((2 * ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0)
    (e4 : g 1 * ((-ω - 2) / 3) + g 2 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((-ω - 2) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-ω + 1) / 3) + g 15 * ((ω + 2) / 3) = 0)
    (e5 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e7 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-2 * ω - 1) / 3) + g 7 * ((-2 * ω - 1) / 3) + g 9 * ((-ω + 1) / 3) + g 11 * ((-ω + 1) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e9 : g 2 * ((-ω - 2) / 3) + g 3 * ((ω + 2) / 3) + g 4 * ((-ω - 2) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω + 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 10 * (-ω - 1) + g 11 * ((ω + 2) / 3) + g 12 * ((ω + 2) / 3) + g 13 * (-ω - 1) + g 14 * ((ω + 2) / 3) + g 15 * (-ω - 1) = 0)
    (e10 : g 0 * 1 + g 1 * 1 + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((-ω - 2) / 3) + g 11 * ((ω - 1) / 3) + g 14 * ((-ω - 2) / 3) = 0)
    (e11 : g 3 * ((ω + 2) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 14 * ((ω + 2) / 3) = 0)
    (e12 : g 1 * ((ω + 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 8 * ((2 * ω + 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) = 0)
    (e13 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((-ω - 2) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e14 : g 3 * ((ω - 1) / 3) + g 4 * ((ω - 1) / 3) + g 5 * ((-ω - 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω - 1) / 3) + g 9 * ((2 * ω + 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-ω + 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0) :
    g 11 = 0 := by
  linear_combination ((-ω - 2) / 3) * e0 + (ω + 1) * e1 + ((-2 * ω - 1) / 3) * e2 + ((ω + 2) / 3) * e3 + ((-2 * ω - 1) / 3) * e4 + ((2 * ω + 1) / 3) * e5 + ((ω + 2) / 3) * e7 + ((ω - 1) / 3) * e9 + ((-ω + 1) / 3) * e10 + ((ω - 1) / 3) * e11 + ((-ω - 2) / 3) * e12 + ((2 * ω + 1) / 3) * e13 + ((-ω + 1) / 3) * e14 - ((1/3) * g 1 + (1/3) * g 2 + (-1/3) * g 3 + (-2/3) * g 7 + (-1) * g 8 + (-1/3) * g 10 + (-2/3) * g 11 + (-1/3) * g 14 + (-1/3) * g 15) * hω

private theorem g32_word_solve_12 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K)
    (e0 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * (-1) + g 4 * ((ω + 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((ω - 1) / 3) + g 10 * 1 + g 11 * ((-ω - 2) / 3) + g 12 * ((ω - 1) / 3) + g 13 * ((ω + 2) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) = 0)
    (e2 : g 2 * ((2 * ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((2 * ω + 1) / 3) + g 7 * ((-ω + 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) + g 15 * ((ω - 1) / 3) = 0)
    (e3 : g 1 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((2 * ω + 1) / 3) + g 8 * ((2 * ω + 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((2 * ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0)
    (e4 : g 1 * ((-ω - 2) / 3) + g 2 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((-ω - 2) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-ω + 1) / 3) + g 15 * ((ω + 2) / 3) = 0)
    (e6 : g 2 * ((-ω - 2) / 3) + g 3 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 10 * ω + g 11 * ((ω - 1) / 3) + g 12 * ((ω + 2) / 3) + g 13 * ((ω - 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e7 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-2 * ω - 1) / 3) + g 7 * ((-2 * ω - 1) / 3) + g 9 * ((-ω + 1) / 3) + g 11 * ((-ω + 1) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e8 : g 2 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e10 : g 0 * 1 + g 1 * 1 + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((-ω - 2) / 3) + g 11 * ((ω - 1) / 3) + g 14 * ((-ω - 2) / 3) = 0)
    (e11 : g 3 * ((ω + 2) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 14 * ((ω + 2) / 3) = 0) :
    g 12 = 0 := by
  linear_combination ((-ω - 2) / 3) * e0 + ((ω - 1) / 3) * e2 + ((-2 * ω - 1) / 3) * e3 + ((-ω + 1) / 3) * e4 + ((-2 * ω - 1) / 3) * e6 + ((ω + 2) / 3) * e7 + ((2 * ω + 1) / 3) * e8 + ((ω + 2) / 3) * e10 + ((ω - 1) / 3) * e11 - ((1/3) * g 1 + (1/3) * g 2 + (1/3) * g 3 + (1/3) * g 4 + (1/3) * g 6 + (-2/3) * g 7 + (-1/3) * g 9 + (-2/3) * g 10 + (-4/3) * g 12 + (-1/3) * g 13 + (1/3) * g 15) * hω

private theorem g32_word_solve_13 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K)
    (e1 : g 1 * ((2 * ω + 1) / 3) + g 2 * ((2 * ω + 1) / 3) + g 4 * ((2 * ω + 1) / 3) + g 6 * ((2 * ω + 1) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e2 : g 2 * ((2 * ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((2 * ω + 1) / 3) + g 7 * ((-ω + 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) + g 15 * ((ω - 1) / 3) = 0)
    (e3 : g 1 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((2 * ω + 1) / 3) + g 8 * ((2 * ω + 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((2 * ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0)
    (e4 : g 1 * ((-ω - 2) / 3) + g 2 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((-ω - 2) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-ω + 1) / 3) + g 15 * ((ω + 2) / 3) = 0)
    (e5 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e7 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-2 * ω - 1) / 3) + g 7 * ((-2 * ω - 1) / 3) + g 9 * ((-ω + 1) / 3) + g 11 * ((-ω + 1) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e8 : g 2 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e10 : g 0 * 1 + g 1 * 1 + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((-ω - 2) / 3) + g 11 * ((ω - 1) / 3) + g 14 * ((-ω - 2) / 3) = 0)
    (e11 : g 3 * ((ω + 2) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 14 * ((ω + 2) / 3) = 0)
    (e12 : g 1 * ((ω + 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 8 * ((2 * ω + 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) = 0)
    (e13 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((-ω - 2) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e14 : g 3 * ((ω - 1) / 3) + g 4 * ((ω - 1) / 3) + g 5 * ((-ω - 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω - 1) / 3) + g 9 * ((2 * ω + 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-ω + 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0) :
    g 13 = 0 := by
  linear_combination ((-ω + 1) / 3) * e1 + ((ω - 1) / 3) * e2 + ((-ω + 1) / 3) * e3 + ((2 * ω + 1) / 3) * e4 + ((ω + 2) / 3) * e5 + ((2 * ω + 1) / 3) * e7 + ((-2 * ω - 1) / 3) * e8 + ((-ω - 2) / 3) * e10 + ((-ω + 1) / 3) * e11 + ((2 * ω + 1) / 3) * e12 + ((-ω + 1) / 3) * e13 + ((2 * ω + 1) / 3) * e14 - ((-2/3) * g 7 + (2/3) * g 8 + (1/3) * g 9 + (-1/3) * g 11 + (-2/3) * g 12 + (-4/3) * g 13 + (2/3) * g 14 + (1/3) * g 15) * hω

private theorem g32_word_solve_14 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K)
    (e0 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * (-1) + g 4 * ((ω + 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((ω - 1) / 3) + g 10 * 1 + g 11 * ((-ω - 2) / 3) + g 12 * ((ω - 1) / 3) + g 13 * ((ω + 2) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) = 0)
    (e1 : g 1 * ((2 * ω + 1) / 3) + g 2 * ((2 * ω + 1) / 3) + g 4 * ((2 * ω + 1) / 3) + g 6 * ((2 * ω + 1) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e2 : g 2 * ((2 * ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((2 * ω + 1) / 3) + g 7 * ((-ω + 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) + g 15 * ((ω - 1) / 3) = 0)
    (e4 : g 1 * ((-ω - 2) / 3) + g 2 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((-ω - 2) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-ω + 1) / 3) + g 15 * ((ω + 2) / 3) = 0)
    (e5 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((ω - 1) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e6 : g 2 * ((-ω - 2) / 3) + g 3 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 10 * ω + g 11 * ((ω - 1) / 3) + g 12 * ((ω + 2) / 3) + g 13 * ((ω - 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e8 : g 2 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e9 : g 2 * ((-ω - 2) / 3) + g 3 * ((ω + 2) / 3) + g 4 * ((-ω - 2) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω + 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 10 * (-ω - 1) + g 11 * ((ω + 2) / 3) + g 12 * ((ω + 2) / 3) + g 13 * (-ω - 1) + g 14 * ((ω + 2) / 3) + g 15 * (-ω - 1) = 0)
    (e10 : g 0 * 1 + g 1 * 1 + g 2 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((-ω - 2) / 3) + g 11 * ((ω - 1) / 3) + g 14 * ((-ω - 2) / 3) = 0) :
    g 14 = 0 := by
  linear_combination ((-2 * ω - 1) / 3) * e0 + ((-2 * ω - 1) / 3) * e1 + ((ω - 1) / 3) * e2 + ((ω + 2) / 3) * e4 + ((ω + 2) / 3) * e5 + ((-2 * ω - 1) / 3) * e6 + ((-2 * ω - 1) / 3) * e8 + ((-2 * ω - 1) / 3) * e9 + ((ω - 1) / 3) * e10 - ((-2/3) * g 1 + (1/3) * g 2 + (-2/3) * g 7 + (2/3) * g 8 + (-1/3) * g 9 + (-1/3) * g 11 + (-2/3) * g 12 + (-2/3) * g 14 + (2/3) * g 15) * hω

private theorem g32_word_solve_15 {K : Type*} [Field K] [CharZero K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Fin 16 → K)
    (e0 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * ((-ω + 1) / 3) + g 3 * (-1) + g 4 * ((ω + 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((-ω - 2) / 3) + g 9 * ((ω - 1) / 3) + g 10 * 1 + g 11 * ((-ω - 2) / 3) + g 12 * ((ω - 1) / 3) + g 13 * ((ω + 2) / 3) + g 14 * ((ω - 1) / 3) + g 15 * ((-ω + 1) / 3) = 0)
    (e1 : g 1 * ((2 * ω + 1) / 3) + g 2 * ((2 * ω + 1) / 3) + g 4 * ((2 * ω + 1) / 3) + g 6 * ((2 * ω + 1) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 14 * ((-2 * ω - 1) / 3) = 0)
    (e2 : g 2 * ((2 * ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((2 * ω + 1) / 3) + g 7 * ((-ω + 1) / 3) + g 9 * ((-2 * ω - 1) / 3) + g 11 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-2 * ω - 1) / 3) + g 15 * ((ω - 1) / 3) = 0)
    (e4 : g 1 * ((-ω - 2) / 3) + g 2 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((-ω - 2) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((-ω + 1) / 3) + g 15 * ((ω + 2) / 3) = 0)
    (e6 : g 2 * ((-ω - 2) / 3) + g 3 * ((-2 * ω - 1) / 3) + g 4 * ((-2 * ω - 1) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((-2 * ω - 1) / 3) + g 10 * ω + g 11 * ((ω - 1) / 3) + g 12 * ((ω + 2) / 3) + g 13 * ((ω - 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e7 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-2 * ω - 1) / 3) + g 7 * ((-2 * ω - 1) / 3) + g 9 * ((-ω + 1) / 3) + g 11 * ((-ω + 1) / 3) + g 12 * ((-ω + 1) / 3) + g 13 * ((-2 * ω - 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((2 * ω + 1) / 3) = 0)
    (e8 : g 2 * ((-ω + 1) / 3) + g 4 * ((-ω + 1) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((ω - 1) / 3) + g 11 * ((ω - 1) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e9 : g 2 * ((-ω - 2) / 3) + g 3 * ((ω + 2) / 3) + g 4 * ((-ω - 2) / 3) + g 5 * ((ω + 2) / 3) + g 7 * ((ω + 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 10 * (-ω - 1) + g 11 * ((ω + 2) / 3) + g 12 * ((ω + 2) / 3) + g 13 * (-ω - 1) + g 14 * ((ω + 2) / 3) + g 15 * (-ω - 1) = 0)
    (e11 : g 3 * ((ω + 2) / 3) + g 5 * ((ω + 2) / 3) + g 6 * ((-ω - 2) / 3) + g 8 * ((ω + 2) / 3) + g 9 * ((ω + 2) / 3) + g 12 * ((-ω + 1) / 3) + g 14 * ((ω + 2) / 3) = 0)
    (e13 : g 1 * ((-ω + 1) / 3) + g 3 * ((-ω - 2) / 3) + g 5 * ((-ω - 2) / 3) + g 6 * ((-ω + 1) / 3) + g 7 * ((-ω - 2) / 3) + g 11 * ((-ω - 2) / 3) + g 12 * ((-ω - 2) / 3) = 0)
    (e14 : g 3 * ((ω - 1) / 3) + g 4 * ((ω - 1) / 3) + g 5 * ((-ω - 2) / 3) + g 7 * ((ω - 1) / 3) + g 8 * ((ω - 1) / 3) + g 9 * ((2 * ω + 1) / 3) + g 12 * ((-ω - 2) / 3) + g 13 * ((-ω + 1) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((-2 * ω - 1) / 3) = 0)
    (e15 : g 0 * 1 + g 1 * ((ω + 2) / 3) + g 2 * 1 + g 3 * ((2 * ω + 1) / 3) + g 4 * ((ω + 2) / 3) + g 6 * ((ω + 2) / 3) + g 7 * ((2 * ω + 1) / 3) + g 8 * ((ω - 1) / 3) + g 9 * ((2 * ω + 1) / 3) + g 10 * (-1) + g 11 * ((ω - 1) / 3) + g 13 * ((-ω - 2) / 3) + g 14 * ((2 * ω + 1) / 3) + g 15 * ((ω - 1) / 3) = 0) :
    g 15 = 0 := by
  linear_combination ((ω - 1) / 3) * e0 + ((ω + 2) / 3) * e1 + ((ω - 1) / 3) * e2 + ((-2 * ω - 1) / 3) * e4 + ((-ω - 2) / 3) * e6 + ((-ω + 1) / 3) * e7 + ((ω - 1) / 3) * e8 + ((2 * ω + 1) / 3) * e9 + ((ω - 1) / 3) * e11 + ((-ω + 1) / 3) * e13 + ((ω - 1) / 3) * e14 + ((-ω + 1) / 3) * e15 - ((2/3) * g 1 + (1/3) * g 2 + (2/3) * g 3 + (1/3) * g 4 + (2/3) * g 6 + (1/3) * g 7 + (1/3) * g 9 + (-1) * g 10 + (1/3) * g 11 + (-1/3) * g 13 + (-5/3) * g 15) * hω

theorem papers_g32_words_linearIndependent_aux {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    LinearIndependent K (fun i => g32WordMat ω (g32SpanWords i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have he : ∀ a b, (∑ i, g i • g32WordMat ω (g32SpanWords i)) a b = 0 := fun a b => by rw [hg]; rfl
  have e0 := (g32_word_coord_0 hω g).symm.trans (he 0 0)
  have e1 := (g32_word_coord_1 hω g).symm.trans (he 0 1)
  have e2 := (g32_word_coord_2 hω g).symm.trans (he 0 2)
  have e3 := (g32_word_coord_3 hω g).symm.trans (he 0 3)
  have e4 := (g32_word_coord_4 hω g).symm.trans (he 1 0)
  have e5 := (g32_word_coord_5 hω g).symm.trans (he 1 1)
  have e6 := (g32_word_coord_6 hω g).symm.trans (he 1 2)
  have e7 := (g32_word_coord_7 hω g).symm.trans (he 1 3)
  have e8 := (g32_word_coord_8 hω g).symm.trans (he 2 0)
  have e9 := (g32_word_coord_9 hω g).symm.trans (he 2 1)
  have e10 := (g32_word_coord_10 hω g).symm.trans (he 2 2)
  have e11 := (g32_word_coord_11 hω g).symm.trans (he 2 3)
  have e12 := (g32_word_coord_12 hω g).symm.trans (he 3 0)
  have e13 := (g32_word_coord_13 hω g).symm.trans (he 3 1)
  have e14 := (g32_word_coord_14 hω g).symm.trans (he 3 2)
  have e15 := (g32_word_coord_15 hω g).symm.trans (he 3 3)
  intro k
  fin_cases k
  · exact g32_word_solve_0 hω g e0 e1 e2 e4 e5 e6 e9 e12 e13 e14
  · exact g32_word_solve_1 hω g e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
  · exact g32_word_solve_2 hω g e0 e2 e3 e4 e5 e6 e7 e8 e9 e10 e12 e13 e14 e15
  · exact g32_word_solve_3 hω g e1 e2 e3 e4 e5 e6 e9 e10 e11 e12 e13 e14 e15
  · exact g32_word_solve_4 hω g e0 e1 e3 e4 e5 e7 e8 e9 e11
  · exact g32_word_solve_5 hω g e0 e1 e2 e3 e4 e6 e7 e8 e9 e10 e11 e12 e13 e14
  · exact g32_word_solve_6 hω g e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
  · exact g32_word_solve_7 hω g e0 e1 e2 e3 e4 e6 e7 e8 e9 e10 e13 e14 e15
  · exact g32_word_solve_8 hω g e1 e2 e3 e5 e6 e7 e9 e10 e11 e13
  · exact g32_word_solve_9 hω g e0 e1 e2 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e15
  · exact g32_word_solve_10 hω g e0 e1 e3 e4 e5 e6 e9 e10 e11 e12 e13 e14 e15
  · exact g32_word_solve_11 hω g e0 e1 e2 e3 e4 e5 e7 e9 e10 e11 e12 e13 e14
  · exact g32_word_solve_12 hω g e0 e2 e3 e4 e6 e7 e8 e10 e11
  · exact g32_word_solve_13 hω g e1 e2 e3 e4 e5 e7 e8 e10 e11 e12 e13 e14
  · exact g32_word_solve_14 hω g e0 e1 e2 e4 e5 e6 e8 e9 e10
  · exact g32_word_solve_15 hω g e0 e1 e2 e4 e6 e7 e8 e9 e11 e13 e14 e15

theorem papers_g32_words_span_aux {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    Submodule.span K (Set.range fun i => g32WordMat ω (g32SpanWords i)) = ⊤ :=
  (papers_g32_words_linearIndependent_aux ω hω).span_eq_top_of_card_eq_finrank (by simp [Module.finrank_matrix])

theorem papers_g32_adjoin_top_aux {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    Algebra.adjoin K {g32R1 ω, g32R2 ω, g32X ω} = ⊤ := by
  rw [eq_top_iff]
  intro A _
  have hA : A ∈ Submodule.span K (Set.range fun i => g32WordMat ω (g32SpanWords i)) := by
    rw [papers_g32_words_span_aux ω hω]; exact Submodule.mem_top
  have hle : Submodule.span K (Set.range fun i => g32WordMat ω (g32SpanWords i)) ≤
      Subalgebra.toSubmodule (Algebra.adjoin K {g32R1 ω, g32R2 ω, g32X ω}) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Subalgebra.list_prod_mem _ fun B hB => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hB
    apply Algebra.subset_adjoin
    fin_cases k <;> simp [g32Gen]
  exact hle hA

theorem papers_g32_words_perturbed_aux {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    ¬ LinearIndependent K (Function.update (fun i => g32WordMat ω (g32SpanWords i)) 15 (g32R1 ω * g32R1 ω)) := by
  rw [Fintype.not_linearIndependent_iff]
  refine ⟨![ω, -(1 + ω), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ?_, 15, by simp⟩
  simp [Fin.sum_univ_succ, Function.update_apply, g32SpanWords, g32WordMat, g32Gen]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g32R1] <;> grind

theorem papers_g32_adjoin_r1_r2_ne_top_aux {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    Algebra.adjoin K {g32R1 ω, g32R2 ω} ≠ ⊤ := by
  let v : Fin 4 → K := ![1, -1 - ω, 1, 0]
  let S : Subalgebra K (Matrix (Fin 4) (Fin 4) K) :=
    { carrier := {A | ∃ c : K, A *ᵥ v = c • v}
      mul_mem' := by
        rintro A B ⟨a, ha⟩ ⟨b, hb⟩
        exact ⟨a * b, by rw [← Matrix.mulVec_mulVec, hb, Matrix.mulVec_smul, ha, smul_smul, mul_comm]⟩
      add_mem' := by
        rintro A B ⟨a, ha⟩ ⟨b, hb⟩
        exact ⟨a + b, by rw [Matrix.add_mulVec, ha, hb, add_smul]⟩
      algebraMap_mem' := fun c => ⟨c, by
        rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]⟩ }
  have hle : Algebra.adjoin K {g32R1 ω, g32R2 ω} ≤ S := by
    rw [Algebra.adjoin_le_iff]
    rintro A (rfl | rfl)
    · refine ⟨1, ?_⟩
      ext i
      fin_cases i <;> simp [v, g32R1, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> grind
    · refine ⟨1, ?_⟩
      ext i
      fin_cases i <;> simp [v, g32R2, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> grind
  intro htop
  obtain ⟨c, hc⟩ : Matrix.single 1 0 (1 : K) ∈ S := hle (htop ▸ Algebra.mem_top)
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  simp [v, Matrix.mulVec, dotProduct, Matrix.single_apply] at h0 h1
  grind

theorem papers_g32_phi_deriv_poly_aux :
    derivative g32PhiNum * g32PhiDen - g32PhiNum * derivative g32PhiDen = 3 * X * (X - 3) ^ 3 * g32CritQuad * (X - 1) ^ 2 * (X + 2) ^ 2 := by
  simp only [g32PhiNum, g32PhiDen, g32CritQuad, derivative_mul, derivative_pow, derivative_sub,
    derivative_add, derivative_X, derivative_ofNat]
  simp only [derivative_one, map_ofNat, Nat.cast_ofNat]
  ring

lemma g32_den_ne (s : ℂ) (h₁ : s ≠ 1) (h₂ : s ≠ -2) : (s - 1) ^ 3 * (s + 2) ^ 3 ≠ 0 := by
  have a : s - 1 ≠ 0 := sub_ne_zero.mpr h₁
  have b : s + 2 ≠ 0 := by
    intro h; apply h₂; linear_combination h
  exact mul_ne_zero (pow_ne_zero _ a) (pow_ne_zero _ b)

theorem papers_g32_phi_hasDerivAt_aux (s : ℂ) (h₁ : s ≠ 1) (h₂ : s ≠ -2) :
    HasDerivAt g32Phi (g32PhiDeriv s) s := by
  have a : s - 1 ≠ 0 := sub_ne_zero.mpr h₁
  have b : s + 2 ≠ 0 := by
    intro h; apply h₂; linear_combination h
  have hN : HasDerivAt (fun x : ℂ => x ^ 2 * (x - 3) ^ 4)
      (2 * s * (s - 3) ^ 4 + s ^ 2 * (4 * (s - 3) ^ 3)) s := by
    have := ((hasDerivAt_id' s).fun_pow 2).fun_mul (((hasDerivAt_id' s).sub_const 3).fun_pow 4)
    convert this using 1
    simp
  have hD : HasDerivAt (fun x : ℂ => (x - 1) ^ 3 * (x + 2) ^ 3)
      (3 * (s - 1) ^ 2 * (s + 2) ^ 3 + (s - 1) ^ 3 * (3 * (s + 2) ^ 2)) s := by
    have := (((hasDerivAt_id' s).sub_const 1).fun_pow 3).fun_mul (((hasDerivAt_id' s).add_const 2).fun_pow 3)
    convert this using 1
    simp
  have := hN.div hD (g32_den_ne s h₁ h₂)
  convert this using 1
  · funext x; simp [g32Phi]
  · unfold g32PhiDeriv
    field_simp
    ring

theorem papers_g32_phi_critical_points_aux (s : ℂ) (h₁ : s ≠ 1) (h₂ : s ≠ -2) :
    g32PhiDeriv s = 0 ↔ s = 0 ∨ s = 3 ∨ 5 * s ^ 2 - 3 * s + 4 = 0 := by
  have a : s - 1 ≠ 0 := sub_ne_zero.mpr h₁
  have b : s + 2 ≠ 0 := by
    intro h; apply h₂; linear_combination h
  have hd : (s - 1) ^ 4 * (s + 2) ^ 4 ≠ 0 := mul_ne_zero (pow_ne_zero _ a) (pow_ne_zero _ b)
  unfold g32PhiDeriv
  rw [div_eq_zero_iff, or_iff_left hd]
  simp only [mul_eq_zero, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    false_or, sub_eq_zero]
  tauto

theorem papers_g32_phi_deriv_poly_perturbed_aux :
    derivative g32PhiNum * g32PhiDen - g32PhiNum * derivative g32PhiDen ≠ 3 * X * (X - 3) ^ 3 * (5 * X ^ 2 + 3 * X + 4) * (X - 1) ^ 2 * (X + 2) ^ 2 := by
  rw [papers_g32_phi_deriv_poly_aux]
  intro h
  have := congrArg (eval (-1 : ℚ)) h
  simp [g32CritQuad] at this
  norm_num at this

theorem papers_g32_crit_value_dvd_aux :
    g32CritQuad ∣ g32CritValuePoly 729 3674 5120 := by
  refine ⟨435*X^10 + 9519*X^9 + 34155*X^8 - 306581*X^7 + 765525*X^6 - 1086515*X^5 + 1035353*X^4 - 734375*X^3 + 415988*X^2 - 184320*X + 81920, ?_⟩
  simp only [g32CritValuePoly, g32CritQuad, g32PhiNum, g32PhiDen, map_ofNat]
  ring

lemma g32_crit_value_div (x y : ℂ) (hy : y ≠ 0) :
    729 * (x / y) ^ 2 - 3674 * (x / y) + 5120 = (729 * x ^ 2 - 3674 * x * y + 5120 * y ^ 2) / y ^ 2 := by
  field_simp

theorem papers_g32_crit_values_aux :
    g32Phi '' {s : ℂ | 5 * s ^ 2 - 3 * s + 4 = 0} = {z : ℂ | 729 * z ^ 2 - 3674 * z + 5120 = 0} := by
  ext z
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨s, hs, rfl⟩
    have h₁ : s ≠ 1 := by rintro rfl; norm_num at hs
    have h₂ : s ≠ -2 := by rintro rfl; norm_num at hs
    have hD := g32_den_ne s h₁ h₂
    unfold g32Phi
    rw [g32_crit_value_div _ _ hD, div_eq_zero_iff]
    left
    linear_combination (435*s^10 + 9519*s^9 + 34155*s^8 - 306581*s^7 + 765525*s^6 - 1086515*s^5 + 1035353*s^4 - 734375*s^3 + 415988*s^2 - 184320*s + 81920) * hs
  · intro hz
    refine ⟨(2050 - 729 * z) / 710, ?_, ?_⟩
    · linear_combination (729/100820 : ℂ) * hz
    · set s : ℂ := (2050 - 729 * z) / 710 with hsdef
      have hs : 5 * s ^ 2 - 3 * s + 4 = 0 := by
        rw [hsdef]; linear_combination (729/100820 : ℂ) * hz
      have h₁ : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
      have h₂ : s ≠ -2 := by intro h; rw [h] at hs; norm_num at hs
      have hD := g32_den_ne s h₁ h₂
      unfold g32Phi
      rw [div_eq_iff hD, hsdef]
      linear_combination ((-205891132094649*z^5/128100283921000000 + 648740645296857*z^4/25620056784200000 - 311369459588811*z^3/2562005678420000 + 15174234341559*z^2/64050141960500 - 98169313149*z/640501419605 + 33620/128100283921) : ℂ) * hz

theorem papers_g32_crit_values_not_real_aux :
    ∀ z : ℂ, 729 * z ^ 2 - 3674 * z + 5120 = 0 → z.im ≠ 0 := by
  intro z hz him
  have h := congrArg Complex.re hz
  simp [pow_two, him] at h
  nlinarith [sq_nonneg (729 * z.re - 1837)]

theorem papers_g32_crit_value_dvd_perturbed_aux :
    ¬ g32CritQuad ∣ g32CritValuePoly 729 3675 5120 := by
  intro h
  have hND : g32CritQuad ∣ g32PhiNum * g32PhiDen := by
    have e : g32PhiNum * g32PhiDen = g32CritValuePoly 729 3674 5120 - g32CritValuePoly 729 3675 5120 := by
      simp only [g32CritValuePoly]
      rw [show (3675 : ℚ) = 3674 + 1 by norm_num, C_add, C_1]
      ring
    rw [e]
    exact dvd_sub papers_g32_crit_value_dvd_aux h
  have hdeg : 0 < degree (g32CritQuad.map (algebraMap ℚ ℂ)) := by
    have h2 : degree g32CritQuad = 2 := by unfold g32CritQuad; compute_degree!
    rw [degree_map, h2]; decide
  obtain ⟨s, hs⟩ := Complex.exists_root hdeg
  have hq : 5 * s ^ 2 - 3 * s + 4 = 0 := by
    simpa [g32CritQuad] using hs
  have h0 : eval s ((g32PhiNum * g32PhiDen).map (algebraMap ℚ ℂ)) = 0 := by
    obtain ⟨r, hr⟩ := hND
    rw [hr, Polynomial.map_mul, eval_mul, hs.eq_zero, zero_mul]
  simp [g32PhiNum, g32PhiDen, sub_eq_zero] at h0
  rcases h0 with ((rfl | rfl) | rfl | h)
  · norm_num at hq
  · norm_num at hq
  · norm_num at hq
  have : s = -2 := by linear_combination h
  subst this; norm_num at hq

theorem papers_g34_exps_selfneg_aux (m : ℕ) (α : List ℕ) (hrange : ∀ a ∈ α, 0 < a ∧ a < m) (a : ℕ) (ha : a ∈ α) (h2 : 2 * a % m = 0) :
    2 * a = m := by
  obtain ⟨h0, hm⟩ := hrange a ha
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h2
  rcases k with _ | _ | k
  · omega
  · omega
  · nlinarith

/-- A flattened list of pairs has twice as many entries as pairs. -/
theorem flatMap_pair_length (L : List (ℕ × ℕ)) :
    (L.flatMap fun p => [p.1, p.2]).length = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons p L ih => simp only [List.flatMap_cons, List.length_append, ih]; simp; ring

/-- An in-range, negation-stable exponent list with sum `0` modulo `m` splits into pairs with sum
exactly `m`. -/
theorem exps_pairs_exist (m : ℕ) : ∀ (n : ℕ) (α : List ℕ), α.length = n → (∀ a ∈ α, 0 < a ∧ a < m) →
    ExpsNegStable m α → α.sum % m = 0 →
    ∃ L : List (ℕ × ℕ), (L.flatMap fun p => [p.1, p.2]).Perm α ∧ ∀ p ∈ L, p.1 + p.2 = m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro α hlen hrange hstable hsum
  unfold ExpsNegStable at hstable
  by_cases hb : ∃ b ∈ α, 2 * b ≠ m
  · obtain ⟨b, hbα, hb2⟩ := hb
    have hbr := hrange b hbα
    have hmb : m - b ∈ α.erase b := by
      have : m - b ∈ α := hstable.subset (List.mem_map.2 ⟨b, hbα, rfl⟩)
      exact (List.mem_erase_of_ne (by omega)).2 this
    set t := (α.erase b).erase (m - b) with ht
    have hp : α.Perm (b :: (m - b) :: t) :=
      (List.perm_cons_erase hbα).trans (List.Perm.cons _ (List.perm_cons_erase hmb))
    have htsub : ∀ a ∈ t, a ∈ α := fun a ha => hp.symm.subset (by simp [ha])
    have htlen : t.length < n := by
      have := hp.length_eq; simp at this; omega
    have htstable : (t.map fun a => m - a).Perm t := by
      have h1 := ((hp.map (fun a => m - a)).symm.trans hstable).trans hp
      simp only [List.map_cons, show m - (m - b) = b by omega] at h1
      exact ((h1.trans (List.Perm.swap _ _ _)).cons_inv).cons_inv
    have htsum : t.sum % m = 0 := by
      have := hp.sum_eq
      simp only [List.sum_cons] at this
      rw [this, show b + (m - b + t.sum) = t.sum + m by omega, Nat.add_mod_right] at hsum
      exact hsum
    obtain ⟨L, hL, hLp⟩ := ih _ htlen t rfl (fun a ha => hrange a (htsub a ha)) htstable htsum
    refine ⟨(b, m - b) :: L, ?_, ?_⟩
    · simp only [List.flatMap_cons, List.cons_append, List.nil_append]
      exact ((hL.cons _).cons _).trans hp.symm
    · intro p hp'
      rcases List.mem_cons.1 hp' with rfl | hp'
      · simp; omega
      · exact hLp p hp'
  · push Not at hb
    match α, hlen, hrange, hstable, hsum, hb with
    | [], _, _, _, _, _ => exact ⟨[], List.Perm.refl _, by simp⟩
    | [x], _, hrange, _, hsum, hb =>
      exfalso
      have h1 := hb x (by simp); have h2 := hrange x (by simp)
      simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
      rw [Nat.mod_eq_of_lt h2.2] at hsum; omega
    | x :: y :: t, hlen, hrange, hstable, hsum, hb =>
      have hx := hb x (by simp); have hy := hb y (by simp)
      have hxr := hrange x (by simp)
      have hyx : y = x := by omega
      subst hyx
      have htlen : t.length < n := by simp at hlen; omega
      have htstable : (t.map fun a => m - a).Perm t := by
        simp only [List.map_cons, show m - y = y by omega] at hstable
        exact hstable.cons_inv.cons_inv
      have htsum : t.sum % m = 0 := by
        simp only [List.sum_cons] at hsum
        rwa [show y + (y + t.sum) = t.sum + m by omega, Nat.add_mod_right] at hsum
      obtain ⟨L, hL, hLp⟩ := ih _ htlen t rfl (fun a ha => hrange a (by simp [ha])) htstable htsum
      refine ⟨(y, y) :: L, ?_, ?_⟩
      · simp only [List.flatMap_cons, List.cons_append, List.nil_append]
        exact (hL.cons _).cons _
      · intro p hp'
        rcases List.mem_cons.1 hp' with rfl | hp'
        · simp; omega
        · exact hLp p hp'

/-- In a flattened list of pairs with sum `m`, the entries `a` with `2a = m` come two at a time. -/
theorem countP_flatMap_pairs_even (m : ℕ) (L : List (ℕ × ℕ)) (hL : ∀ p ∈ L, p.1 + p.2 = m) :
    Even ((L.flatMap fun p => [p.1, p.2]).countP fun a => 2 * a = m) := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.flatMap_cons, List.countP_append]
    have hp := hL p (by simp)
    refine Even.add ?_ (ih fun q hq => hL q (by simp [hq]))
    by_cases h : 2 * p.1 = m
    · have h' : 2 * p.2 = m := by omega
      simp [h, h']
    · have h' : ¬ 2 * p.2 = m := by omega
      simp [h, h']

theorem papers_g34_exps_unpaired_even_aux (m : ℕ) (α : List ℕ) (hrange : ∀ a ∈ α, 0 < a ∧ a < m) (hstable : ExpsNegStable m α) (hsum : α.sum % m = 0) :
    Even (α.countP fun a => 2 * a = m) := by
  obtain ⟨L, hL, hLp⟩ := exps_pairs_exist m _ α rfl hrange hstable hsum
  rw [← hL.countP_eq]
  exact countP_flatMap_pairs_even m L hLp

theorem papers_g34_exps_simple_aux (m : ℕ) (α : List ℕ) (hrange : ∀ a ∈ α, 0 < a ∧ a < m) (hstable : ExpsNegStable m α) (hsum : α.sum % m = 0) :
    IsSimpleExps m α := by
  obtain ⟨L, hL, hLp⟩ := exps_pairs_exist m _ α rfl hrange hstable hsum
  exact ⟨L, hL, fun p hp => by rw [hLp p hp, Nat.mod_self]⟩

theorem papers_g34_exps_length_even_aux (m : ℕ) (α : List ℕ) (hrange : ∀ a ∈ α, 0 < a ∧ a < m) (hstable : ExpsNegStable m α) (hsum : α.sum % m = 0) :
    Even α.length := by
  obtain ⟨L, hL, -⟩ := exps_pairs_exist m _ α rfl hrange hstable hsum
  rw [← hL.length_eq, flatMap_pair_length]
  exact even_two_mul _

theorem papers_g34_real_supplier_admissible_aux (m q : ℕ) (α : List ℕ) (hrange : ∀ a ∈ α, 0 < a ∧ a < m) (hstable : ExpsNegStable m α) (hsum : α.sum % m = 0) (hh : 0 < (2 * q - 2 + α.length : ℤ)) :
    SupplierAdmissible m q α := by
  obtain ⟨k, hk⟩ := papers_g34_exps_length_even_aux m α hrange hstable hsum
  refine ⟨hh, ⟨(q : ℤ) - 1 + k, by rw [hk]; push_cast; ring⟩,
    papers_g34_exps_simple_aux m α hrange hstable hsum⟩

/-- A list of odd length is not simple. -/
theorem not_isSimpleExps_of_odd (m : ℕ) (α : List ℕ) (h : ¬ Even α.length) : ¬ IsSimpleExps m α := by
  rintro ⟨L, hL, -⟩
  rw [← hL.length_eq, flatMap_pair_length] at h
  exact h (even_two_mul _)

theorem papers_g34_exps_sum_needed_aux :
    (∀ a ∈ [2], 0 < a ∧ a < 4) ∧ ExpsNegStable 4 [2] ∧ [2].sum % 4 ≠ 0 ∧ ¬ IsSimpleExps 4 [2] := by
  refine ⟨by decide, by unfold ExpsNegStable; decide, by decide, not_isSimpleExps_of_odd _ _ (by decide)⟩

theorem papers_g34_exps_stable_needed_aux :
    (∀ a ∈ [1, 1, 1], 0 < a ∧ a < 3) ∧ ¬ ExpsNegStable 3 [1, 1, 1] ∧ [1, 1, 1].sum % 3 = 0 ∧ ¬ IsSimpleExps 3 [1, 1, 1] := by
  refine ⟨by decide, by unfold ExpsNegStable; decide, by decide, not_isSimpleExps_of_odd _ _ (by decide)⟩

end HodgeLean.Papers
