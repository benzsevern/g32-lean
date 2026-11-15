import HodgeLean.Foundations.Program.PrymVariationDefs
import HodgeLean.Papers.PapersG32Certificates

/-! # Arithmetic helpers for the B6-3a root -/

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
theorem b63_generator_zero_cube : (b4b_generators 0) ^ 3 = 1 := by
  have hc : g32h_omega ^ 3 = 1 := by
    linear_combination (g32h_omega - 1) * g32h_omega_sq_add
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b4b_generators, pow_three, g32R1, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp <;> ring_nf <;>
    simp only [show g32h_omega ^ 2 = -g32h_omega - 1 by
      linear_combination g32h_omega_sq_add, hc] <;> ring

set_option maxHeartbeats 400000 in
theorem b63_generator_one_cube : (b4b_generators 1) ^ 3 = 1 := by
  have hc : g32h_omega ^ 3 = 1 := by
    linear_combination (g32h_omega - 1) * g32h_omega_sq_add
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b4b_generators, pow_three, g32R2, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp <;> ring_nf <;>
    simp only [show g32h_omega ^ 2 = -g32h_omega - 1 by
      linear_combination g32h_omega_sq_add, hc] <;> ring

theorem b63_generator_two_fourth : (b4b_generators 2) ^ 4 = 1 := by
  apply Subtype.ext
  simpa [b4b_generators] using (papers_g32_x_sq g32h_omega g32h_omega_sq_add).2

theorem b63_generator_three_cube : (b4b_generators 3) ^ 3 = 1 := by
  apply Subtype.ext
  simpa [b4b_generators] using
    (papers_g32_y_charpoly g32h_omega g32h_omega_sq_add).2.1

theorem b63_generator_zero_inv : (b4b_generators 0)⁻¹ = (b4b_generators 0) ^ 2 := by
  calc
    (b4b_generators 0)⁻¹ = (b4b_generators 0)⁻¹ * 1 := by simp
    _ = (b4b_generators 0)⁻¹ * (b4b_generators 0) ^ 3 := by
      rw [b63_generator_zero_cube]
    _ = (b4b_generators 0) ^ 2 := by group

theorem b63_generator_one_inv : (b4b_generators 1)⁻¹ = (b4b_generators 1) ^ 2 := by
  calc
    (b4b_generators 1)⁻¹ = (b4b_generators 1)⁻¹ * 1 := by simp
    _ = (b4b_generators 1)⁻¹ * (b4b_generators 1) ^ 3 := by
      rw [b63_generator_one_cube]
    _ = (b4b_generators 1) ^ 2 := by group

theorem b63_generator_two_inv : (b4b_generators 2)⁻¹ = (b4b_generators 2) ^ 3 := by
  calc
    (b4b_generators 2)⁻¹ = (b4b_generators 2)⁻¹ * 1 := by simp
    _ = (b4b_generators 2)⁻¹ * (b4b_generators 2) ^ 4 := by
      rw [b63_generator_two_fourth]
    _ = (b4b_generators 2) ^ 3 := by group

theorem b63_generator_three_inv : (b4b_generators 3)⁻¹ = (b4b_generators 3) ^ 2 := by
  calc
    (b4b_generators 3)⁻¹ = (b4b_generators 3)⁻¹ * 1 := by simp
    _ = (b4b_generators 3)⁻¹ * (b4b_generators 3) ^ 3 := by
      rw [b63_generator_three_cube]
    _ = (b4b_generators 3) ^ 2 := by group

def b63_tail_lhs : b4b_Group :=
  b4b_root 8 * b4b_root 9 * b4b_root 10 * b4b_root 11

def b63_tail_expanded : b4b_Group :=
  let a := b4b_generators 0
  let b := b4b_generators 1
  let x := b4b_generators 2
  let y := b4b_generators 3
  b * y * b * a * b ^ 2 * y ^ 2 * b ^ 2 * a ^ (-4 : ℤ) * x ^ (-3 : ℤ) * a ^ 2 *
    x ^ 3 * a ^ 4 * y * x * a * b ^ (-2 : ℤ) * a ^ 2 * b ^ 2 * x ^ 3 * y ^ 2

theorem b63_tail_expansion : b63_tail_lhs = b63_tail_expanded := by
  simp [b63_tail_lhs, b63_tail_expanded, b4b_root, b4b_reflection,
    b63_generator_zero_inv, b63_generator_one_inv, b63_generator_two_inv,
    b63_generator_three_inv]
  group

def b63_tail_positive : b4b_Group :=
  let a := b4b_generators 0
  let b := b4b_generators 1
  let x := b4b_generators 2
  let y := b4b_generators 3
  b * y * b * a * b ^ 2 * y ^ 2 * b ^ 2 * (a ^ 2) ^ 4 * (x ^ 3) ^ 3 * a ^ 2 *
    x ^ 3 * a ^ 4 * y * x * a * (b ^ 2) ^ 2 * a ^ 2 * b ^ 2 * x ^ 3 * y ^ 2

theorem b63_tail_positive_eq : b63_tail_expanded = b63_tail_positive := by
  have h0 : ((b4b_generators 0) ^ 4)⁻¹ = ((b4b_generators 0) ^ 2) ^ 4 := by
    rw [← inv_pow, b63_generator_zero_inv]
  have h2 : ((b4b_generators 2) ^ 3)⁻¹ = ((b4b_generators 2) ^ 3) ^ 3 := by
    rw [← inv_pow, b63_generator_two_inv]
  have h1 : ((b4b_generators 1) ^ 2)⁻¹ = ((b4b_generators 1) ^ 2) ^ 2 := by
    rw [← inv_pow, b63_generator_one_inv]
  simp [b63_tail_expanded, b63_tail_positive, zpow_neg, h0, h1, h2]

def b63_root_eight_word : b4b_Group :=
  let a := b4b_generators 0
  let b := b4b_generators 1
  let y := b4b_generators 3
  b * y * b * a * b ^ 2 * y ^ 2 * b ^ 2

theorem b63_root_eight_expansion : b4b_root 8 = b63_root_eight_word := by
  simp [b63_root_eight_word, b4b_root, b4b_reflection, b63_generator_one_inv,
    b63_generator_three_inv]
  group

def b63_root_nine_word : b4b_Group :=
  let a := b4b_generators 0
  let x := b4b_generators 2
  (a ^ 2) ^ 4 * (x ^ 3) ^ 3 * a ^ 2 * x ^ 3 * a ^ 4

def b63_root_nine_raw : b4b_Group :=
  let a := b4b_generators 0
  let x := b4b_generators 2
  a ^ (-4 : ℤ) * x ^ (-3 : ℤ) * a ^ 2 * x ^ 3 * a ^ 4

theorem b63_root_nine_raw_expansion : b4b_root 9 = b63_root_nine_raw := by
  simp [b63_root_nine_raw, b4b_root, b4b_reflection, b63_generator_zero_inv,
    b63_generator_two_inv]
  group

theorem b63_root_nine_raw_eq : b63_root_nine_raw = b63_root_nine_word := by
  have h0 : ((b4b_generators 0) ^ 4)⁻¹ = ((b4b_generators 0) ^ 2) ^ 4 := by
    rw [← inv_pow, b63_generator_zero_inv]
  have h2 : ((b4b_generators 2) ^ 3)⁻¹ = ((b4b_generators 2) ^ 3) ^ 3 := by
    rw [← inv_pow, b63_generator_two_inv]
  simp [b63_root_nine_raw, b63_root_nine_word, zpow_neg, h0, h2]

theorem b63_root_nine_expansion : b4b_root 9 = b63_root_nine_word :=
  b63_root_nine_raw_expansion.trans b63_root_nine_raw_eq

theorem b63_omega_seven : g32h_omega ^ 7 = g32h_omega := by
  calc
    g32h_omega ^ 7 = g32h_omega ^ 6 * g32h_omega := by ring
    _ = 1 * g32h_omega := by rw [(papers3b_omega_pow _ g32h_omega_sq_add).2.2.2.2]
    _ = g32h_omega := one_mul _

theorem b63_omega_eight : g32h_omega ^ 8 = g32h_omega ^ 2 := by
  calc
    g32h_omega ^ 8 = g32h_omega ^ 6 * g32h_omega ^ 2 := by ring
    _ = 1 * g32h_omega ^ 2 := by rw [(papers3b_omega_pow _ g32h_omega_sq_add).2.2.2.2]
    _ = g32h_omega ^ 2 := one_mul _

theorem b63_omega_nine : g32h_omega ^ 9 = 1 := by
  calc
    g32h_omega ^ 9 = (g32h_omega ^ 3) ^ 3 := by ring
    _ = 1 := by rw [(papers3b_omega_pow _ g32h_omega_sq_add).2.1]; norm_num

theorem b63_omega_ten : g32h_omega ^ 10 = g32h_omega := by
  calc
    g32h_omega ^ 10 = g32h_omega ^ 9 * g32h_omega := by ring
    _ = g32h_omega := by rw [b63_omega_nine, one_mul]

theorem b63_omega_eleven : g32h_omega ^ 11 = g32h_omega ^ 2 := by
  calc
    g32h_omega ^ 11 = g32h_omega ^ 9 * g32h_omega ^ 2 := by ring
    _ = g32h_omega ^ 2 := by rw [b63_omega_nine, one_mul]

theorem b63_omega_twelve : g32h_omega ^ 12 = 1 := by
  calc
    g32h_omega ^ 12 = (g32h_omega ^ 3) ^ 4 := by ring
    _ = 1 := by rw [(papers3b_omega_pow _ g32h_omega_sq_add).2.1]; norm_num

def b63_root_eight_matrix : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, (2 + g32h_omega) / 3, (1 + 2 * g32h_omega) / 3,
       (-1 + g32h_omega) / 3;
     0, (-2 - g32h_omega) / 3, (2 + g32h_omega) / 3,
       (-2 - g32h_omega) / 3;
     0, (-1 + g32h_omega) / 3, (1 + 2 * g32h_omega) / 3,
       (2 + g32h_omega) / 3]


local macro "b63_root_eight_calc" : tactic =>
  `(tactic| (rw [b63_root_eight_expansion] <;>
    simp [b63_root_eight_word, b63_root_eight_matrix, b4b_generators, b4b_toMatrix, pow_two,
      g32R1, g32R2, g32X, g32Y, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_four] <;>
    ring_nf <;>
    all_goals (try simp only [b63_omega_seven, b63_omega_eight, b63_omega_nine,
      b63_omega_ten,
      (papers3b_omega_pow g32h_omega g32h_omega_sq_add).1,
      (papers3b_omega_pow g32h_omega g32h_omega_sq_add).2.1,
      (papers3b_omega_pow g32h_omega g32h_omega_sq_add).2.2.1,
      (papers3b_omega_pow g32h_omega g32h_omega_sq_add).2.2.2.1,
      (papers3b_omega_pow g32h_omega g32h_omega_sq_add).2.2.2.2]) <;>
    all_goals ring_nf))

set_option maxHeartbeats 400000 in
theorem b63_root_eight_entry_0_0 :
    b4b_toMatrix (b4b_root 8) 0 0 = b63_root_eight_matrix 0 0 := by
  b63_root_eight_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eight_entry_0_1 :
    b4b_toMatrix (b4b_root 8) 0 1 = b63_root_eight_matrix 0 1 := by
  b63_root_eight_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eight_entry_0_2 :
    b4b_toMatrix (b4b_root 8) 0 2 = b63_root_eight_matrix 0 2 := by
  b63_root_eight_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eight_entry_0_3 :
    b4b_toMatrix (b4b_root 8) 0 3 = b63_root_eight_matrix 0 3 := by
  b63_root_eight_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eight_entry_1_0 :
    b4b_toMatrix (b4b_root 8) 1 0 = b63_root_eight_matrix 1 0 := by
  b63_root_eight_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eight_entry_1_1 :
    b4b_toMatrix (b4b_root 8) 1 1 = b63_root_eight_matrix 1 1 := by
  b63_root_eight_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eight_entry_1_2 :
    b4b_toMatrix (b4b_root 8) 1 2 = b63_root_eight_matrix 1 2 := by
  b63_root_eight_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eight_entry_1_3 :
    b4b_toMatrix (b4b_root 8) 1 3 = b63_root_eight_matrix 1 3 := by
  b63_root_eight_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eight_entry_2_0 :
    b4b_toMatrix (b4b_root 8) 2 0 = b63_root_eight_matrix 2 0 := by
  b63_root_eight_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eight_entry_2_1 :
    b4b_toMatrix (b4b_root 8) 2 1 = b63_root_eight_matrix 2 1 := by
  b63_root_eight_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eight_entry_2_2 :
    b4b_toMatrix (b4b_root 8) 2 2 = b63_root_eight_matrix 2 2 := by
  b63_root_eight_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eight_entry_2_3 :
    b4b_toMatrix (b4b_root 8) 2 3 = b63_root_eight_matrix 2 3 := by
  b63_root_eight_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eight_entry_3_0 :
    b4b_toMatrix (b4b_root 8) 3 0 = b63_root_eight_matrix 3 0 := by
  b63_root_eight_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eight_entry_3_1 :
    b4b_toMatrix (b4b_root 8) 3 1 = b63_root_eight_matrix 3 1 := by
  b63_root_eight_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eight_entry_3_2 :
    b4b_toMatrix (b4b_root 8) 3 2 = b63_root_eight_matrix 3 2 := by
  b63_root_eight_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eight_entry_3_3 :
    b4b_toMatrix (b4b_root 8) 3 3 = b63_root_eight_matrix 3 3 := by
  b63_root_eight_calc

theorem b63_root_eight_row_zero :
    b4b_toMatrix (b4b_root 8) 0 = b63_root_eight_matrix 0 := by
  funext j
  fin_cases j
  · exact b63_root_eight_entry_0_0
  · exact b63_root_eight_entry_0_1
  · exact b63_root_eight_entry_0_2
  · exact b63_root_eight_entry_0_3

theorem b63_root_eight_row_one :
    b4b_toMatrix (b4b_root 8) 1 = b63_root_eight_matrix 1 := by
  funext j
  fin_cases j
  · exact b63_root_eight_entry_1_0
  · exact b63_root_eight_entry_1_1
  · exact b63_root_eight_entry_1_2
  · exact b63_root_eight_entry_1_3

theorem b63_root_eight_row_two :
    b4b_toMatrix (b4b_root 8) 2 = b63_root_eight_matrix 2 := by
  funext j
  fin_cases j
  · exact b63_root_eight_entry_2_0
  · exact b63_root_eight_entry_2_1
  · exact b63_root_eight_entry_2_2
  · exact b63_root_eight_entry_2_3

theorem b63_root_eight_row_three :
    b4b_toMatrix (b4b_root 8) 3 = b63_root_eight_matrix 3 := by
  funext j
  fin_cases j
  · exact b63_root_eight_entry_3_0
  · exact b63_root_eight_entry_3_1
  · exact b63_root_eight_entry_3_2
  · exact b63_root_eight_entry_3_3

theorem b63_root_eight_matrix_eq :
    b4b_toMatrix (b4b_root 8) = b63_root_eight_matrix := by
  funext i
  fin_cases i
  · exact b63_root_eight_row_zero
  · exact b63_root_eight_row_one
  · exact b63_root_eight_row_two
  · exact b63_root_eight_row_three

def b63_root_nine_short : b4b_Group :=
  let a := b4b_generators 0
  let x := b4b_generators 2
  a ^ 2 * x * a ^ 2 * x ^ 3 * a

theorem b63_root_nine_short_eq : b63_root_nine_word = b63_root_nine_short := by
  have ha : ((b4b_generators 0) ^ 2) ^ 4 = (b4b_generators 0) ^ 2 := by
    calc
      ((b4b_generators 0) ^ 2) ^ 4 = (b4b_generators 0) ^ 3 *
          (b4b_generators 0) ^ 3 * (b4b_generators 0) ^ 2 := by group
      _ = (b4b_generators 0) ^ 2 := by rw [b63_generator_zero_cube]; simp
  have hx : ((b4b_generators 2) ^ 3) ^ 3 = b4b_generators 2 := by
    calc
      ((b4b_generators 2) ^ 3) ^ 3 = (b4b_generators 2) ^ 4 *
          (b4b_generators 2) ^ 4 * b4b_generators 2 := by group
      _ = b4b_generators 2 := by rw [b63_generator_two_fourth]; simp
  have ha4 : (b4b_generators 0) ^ 4 = b4b_generators 0 := by
    calc
      (b4b_generators 0) ^ 4 = (b4b_generators 0) ^ 3 * b4b_generators 0 := by group
      _ = b4b_generators 0 := by rw [b63_generator_zero_cube]; simp
  simp [b63_root_nine_word, b63_root_nine_short, ha, hx, ha4]

def b63_root_nine_matrix : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1 - g32h_omega]


local macro "b63_root_nine_calc" : tactic =>
  `(tactic| (rw [b63_root_nine_expansion, b63_root_nine_short_eq] <;>
    simp [b63_root_nine_short, b63_root_nine_matrix, b4b_generators, b4b_toMatrix,
      pow_two, pow_three, g32R1, g32R2, g32X, g32Y, Matrix.vecMul_apply_eq_sum,
      Fin.sum_univ_four] <;>
    ring_nf <;>
    all_goals (try simp only [b63_omega_seven, b63_omega_eight, b63_omega_nine,
      b63_omega_ten,
      (papers3b_omega_pow g32h_omega g32h_omega_sq_add).1,
      (papers3b_omega_pow g32h_omega g32h_omega_sq_add).2.1,
      (papers3b_omega_pow g32h_omega g32h_omega_sq_add).2.2.1,
      (papers3b_omega_pow g32h_omega g32h_omega_sq_add).2.2.2.1,
      (papers3b_omega_pow g32h_omega g32h_omega_sq_add).2.2.2.2]) <;>
    all_goals ring_nf))

set_option maxHeartbeats 400000 in
theorem b63_root_nine_entry_0_0 :
    b4b_toMatrix (b4b_root 9) 0 0 = b63_root_nine_matrix 0 0 := by
  b63_root_nine_calc

set_option maxHeartbeats 400000 in
theorem b63_root_nine_entry_0_1 :
    b4b_toMatrix (b4b_root 9) 0 1 = b63_root_nine_matrix 0 1 := by
  b63_root_nine_calc

set_option maxHeartbeats 400000 in
theorem b63_root_nine_entry_0_2 :
    b4b_toMatrix (b4b_root 9) 0 2 = b63_root_nine_matrix 0 2 := by
  b63_root_nine_calc

set_option maxHeartbeats 400000 in
theorem b63_root_nine_entry_0_3 :
    b4b_toMatrix (b4b_root 9) 0 3 = b63_root_nine_matrix 0 3 := by
  b63_root_nine_calc

set_option maxHeartbeats 400000 in
theorem b63_root_nine_entry_1_0 :
    b4b_toMatrix (b4b_root 9) 1 0 = b63_root_nine_matrix 1 0 := by
  b63_root_nine_calc

set_option maxHeartbeats 400000 in
theorem b63_root_nine_entry_1_1 :
    b4b_toMatrix (b4b_root 9) 1 1 = b63_root_nine_matrix 1 1 := by
  b63_root_nine_calc

set_option maxHeartbeats 400000 in
theorem b63_root_nine_entry_1_2 :
    b4b_toMatrix (b4b_root 9) 1 2 = b63_root_nine_matrix 1 2 := by
  b63_root_nine_calc

set_option maxHeartbeats 400000 in
theorem b63_root_nine_entry_1_3 :
    b4b_toMatrix (b4b_root 9) 1 3 = b63_root_nine_matrix 1 3 := by
  b63_root_nine_calc

set_option maxHeartbeats 400000 in
theorem b63_root_nine_entry_2_0 :
    b4b_toMatrix (b4b_root 9) 2 0 = b63_root_nine_matrix 2 0 := by
  b63_root_nine_calc

set_option maxHeartbeats 400000 in
theorem b63_root_nine_entry_2_1 :
    b4b_toMatrix (b4b_root 9) 2 1 = b63_root_nine_matrix 2 1 := by
  b63_root_nine_calc

set_option maxHeartbeats 400000 in
theorem b63_root_nine_entry_2_2 :
    b4b_toMatrix (b4b_root 9) 2 2 = b63_root_nine_matrix 2 2 := by
  b63_root_nine_calc

set_option maxHeartbeats 400000 in
theorem b63_root_nine_entry_2_3 :
    b4b_toMatrix (b4b_root 9) 2 3 = b63_root_nine_matrix 2 3 := by
  b63_root_nine_calc

set_option maxHeartbeats 400000 in
theorem b63_root_nine_entry_3_0 :
    b4b_toMatrix (b4b_root 9) 3 0 = b63_root_nine_matrix 3 0 := by
  b63_root_nine_calc

set_option maxHeartbeats 400000 in
theorem b63_root_nine_entry_3_1 :
    b4b_toMatrix (b4b_root 9) 3 1 = b63_root_nine_matrix 3 1 := by
  b63_root_nine_calc

set_option maxHeartbeats 400000 in
theorem b63_root_nine_entry_3_2 :
    b4b_toMatrix (b4b_root 9) 3 2 = b63_root_nine_matrix 3 2 := by
  b63_root_nine_calc

set_option maxHeartbeats 400000 in
theorem b63_root_nine_entry_3_3 :
    b4b_toMatrix (b4b_root 9) 3 3 = b63_root_nine_matrix 3 3 := by
  b63_root_nine_calc

theorem b63_root_nine_row_zero :
    b4b_toMatrix (b4b_root 9) 0 = b63_root_nine_matrix 0 := by
  funext j
  fin_cases j
  · exact b63_root_nine_entry_0_0
  · exact b63_root_nine_entry_0_1
  · exact b63_root_nine_entry_0_2
  · exact b63_root_nine_entry_0_3

theorem b63_root_nine_row_one :
    b4b_toMatrix (b4b_root 9) 1 = b63_root_nine_matrix 1 := by
  funext j
  fin_cases j
  · exact b63_root_nine_entry_1_0
  · exact b63_root_nine_entry_1_1
  · exact b63_root_nine_entry_1_2
  · exact b63_root_nine_entry_1_3

theorem b63_root_nine_row_two :
    b4b_toMatrix (b4b_root 9) 2 = b63_root_nine_matrix 2 := by
  funext j
  fin_cases j
  · exact b63_root_nine_entry_2_0
  · exact b63_root_nine_entry_2_1
  · exact b63_root_nine_entry_2_2
  · exact b63_root_nine_entry_2_3

theorem b63_root_nine_row_three :
    b4b_toMatrix (b4b_root 9) 3 = b63_root_nine_matrix 3 := by
  funext j
  fin_cases j
  · exact b63_root_nine_entry_3_0
  · exact b63_root_nine_entry_3_1
  · exact b63_root_nine_entry_3_2
  · exact b63_root_nine_entry_3_3

theorem b63_root_nine_matrix_eq :
    b4b_toMatrix (b4b_root 9) = b63_root_nine_matrix := by
  funext i
  fin_cases i
  · exact b63_root_nine_row_zero
  · exact b63_root_nine_row_one
  · exact b63_root_nine_row_two
  · exact b63_root_nine_row_three

def b63_root_ten_word : b4b_Group :=
  let a := b4b_generators 0
  let x := b4b_generators 2
  let y := b4b_generators 3
  y * x * a * x ^ 3 * y ^ 2

theorem b63_root_ten_expansion : b4b_root 10 = b63_root_ten_word := by
  simp [b63_root_ten_word, b4b_root, b4b_reflection, b63_generator_two_inv,
    b63_generator_three_inv]
  group

def b63_root_eleven_word : b4b_Group :=
  let a := b4b_generators 0
  let b := b4b_generators 1
  let x := b4b_generators 2
  let y := b4b_generators 3
  (y ^ 2) ^ 2 * (x ^ 3) ^ 3 * (b ^ 2) ^ 2 * a ^ 2 * b ^ 2 * x ^ 3 * y ^ 2

def b63_root_eleven_raw : b4b_Group :=
  let a := b4b_generators 0
  let b := b4b_generators 1
  let x := b4b_generators 2
  let y := b4b_generators 3
  y ^ (-2 : ℤ) * x ^ (-3 : ℤ) * b ^ (-2 : ℤ) * a ^ 2 * b ^ 2 * x ^ 3 * y ^ 2

theorem b63_root_eleven_raw_expansion : b4b_root 11 = b63_root_eleven_raw := by
  simp [b63_root_eleven_raw, b4b_root, b4b_reflection, b63_generator_zero_inv,
    b63_generator_one_inv, b63_generator_two_inv, b63_generator_three_inv]
  group

theorem b63_root_eleven_raw_eq : b63_root_eleven_raw = b63_root_eleven_word := by
  have hy : ((b4b_generators 3) ^ 2)⁻¹ = ((b4b_generators 3) ^ 2) ^ 2 := by
    rw [← inv_pow, b63_generator_three_inv]
  have hx : ((b4b_generators 2) ^ 3)⁻¹ = ((b4b_generators 2) ^ 3) ^ 3 := by
    rw [← inv_pow, b63_generator_two_inv]
  have hb : ((b4b_generators 1) ^ 2)⁻¹ = ((b4b_generators 1) ^ 2) ^ 2 := by
    rw [← inv_pow, b63_generator_one_inv]
  simp [b63_root_eleven_raw, b63_root_eleven_word, zpow_neg, hy, hx, hb]

theorem b63_root_eleven_expansion : b4b_root 11 = b63_root_eleven_word :=
  b63_root_eleven_raw_expansion.trans b63_root_eleven_raw_eq

def b63_root_eleven_short : b4b_Group :=
  let a := b4b_generators 0
  let b := b4b_generators 1
  let x := b4b_generators 2
  let y := b4b_generators 3
  y * x * b * a ^ 2 * b ^ 2 * x ^ 3 * y ^ 2

theorem b63_root_eleven_short_eq : b63_root_eleven_word = b63_root_eleven_short := by
  have hy : ((b4b_generators 3) ^ 2) ^ 2 = b4b_generators 3 := by
    calc
      ((b4b_generators 3) ^ 2) ^ 2 = (b4b_generators 3) ^ 3 *
          b4b_generators 3 := by group
      _ = b4b_generators 3 := by rw [b63_generator_three_cube]; simp
  have hx : ((b4b_generators 2) ^ 3) ^ 3 = b4b_generators 2 := by
    calc
      ((b4b_generators 2) ^ 3) ^ 3 = (b4b_generators 2) ^ 4 *
          (b4b_generators 2) ^ 4 * b4b_generators 2 := by group
      _ = b4b_generators 2 := by rw [b63_generator_two_fourth]; simp
  have hb : ((b4b_generators 1) ^ 2) ^ 2 = b4b_generators 1 := by
    calc
      ((b4b_generators 1) ^ 2) ^ 2 = (b4b_generators 1) ^ 3 *
          b4b_generators 1 := by group
      _ = b4b_generators 1 := by rw [b63_generator_one_cube]; simp
  simp [b63_root_eleven_word, b63_root_eleven_short, hy, hx, hb]

def b63_root_ten_matrix : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, (2 + g32h_omega) / 3, (1 + 2 * g32h_omega) / 3,
       (2 + g32h_omega) / 3;
     0, (-2 - g32h_omega) / 3, (2 + g32h_omega) / 3,
       (1 + 2 * g32h_omega) / 3;
     0, (-1 - 2 * g32h_omega) / 3, (-2 - g32h_omega) / 3,
       (2 + g32h_omega) / 3]

def b63_root_eleven_matrix : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, (1 - g32h_omega) / 3, (-1 + g32h_omega) / 3,
       (1 - g32h_omega) / 3;
     0, (-1 - 2 * g32h_omega) / 3, (1 - g32h_omega) / 3,
       (2 + g32h_omega) / 3;
     0, (1 + 2 * g32h_omega) / 3, (2 + g32h_omega) / 3,
       (1 - g32h_omega) / 3]

local macro "b63_reduce_omega" : tactic =>
  `(tactic| (ring_nf <;>
    all_goals (try simp only [b63_omega_seven, b63_omega_eight, b63_omega_nine,
      b63_omega_ten, b63_omega_eleven, b63_omega_twelve,
      (papers3b_omega_pow g32h_omega g32h_omega_sq_add).1,
      (papers3b_omega_pow g32h_omega g32h_omega_sq_add).2.1,
      (papers3b_omega_pow g32h_omega g32h_omega_sq_add).2.2.1,
      (papers3b_omega_pow g32h_omega g32h_omega_sq_add).2.2.2.1,
      (papers3b_omega_pow g32h_omega g32h_omega_sq_add).2.2.2.2]) <;>
    all_goals ring_nf))

local macro "b63_root_ten_calc" : tactic =>
  `(tactic| (rw [b63_root_ten_expansion] <;>
    simp [b63_root_ten_word, b63_root_ten_matrix, b4b_generators, b4b_toMatrix,
      pow_two, pow_three, g32R1, g32R2, g32X, g32Y, Matrix.vecMul_apply_eq_sum,
      Fin.sum_univ_four] <;> b63_reduce_omega))

local macro "b63_root_eleven_calc" : tactic =>
  `(tactic| (rw [b63_root_eleven_expansion, b63_root_eleven_short_eq] <;>
    simp [b63_root_eleven_short, b63_root_eleven_matrix, b4b_generators, b4b_toMatrix,
      pow_two, pow_three, g32R1, g32R2, g32X, g32Y, Matrix.vecMul_apply_eq_sum,
      Fin.sum_univ_four] <;> b63_reduce_omega))

set_option maxHeartbeats 400000 in
theorem b63_root_ten_entry_0_0 :
    b4b_toMatrix (b4b_root 10) 0 0 = b63_root_ten_matrix 0 0 := by
  b63_root_ten_calc

set_option maxHeartbeats 400000 in
theorem b63_root_ten_entry_0_1 :
    b4b_toMatrix (b4b_root 10) 0 1 = b63_root_ten_matrix 0 1 := by
  b63_root_ten_calc

set_option maxHeartbeats 400000 in
theorem b63_root_ten_entry_0_2 :
    b4b_toMatrix (b4b_root 10) 0 2 = b63_root_ten_matrix 0 2 := by
  b63_root_ten_calc

set_option maxHeartbeats 400000 in
theorem b63_root_ten_entry_0_3 :
    b4b_toMatrix (b4b_root 10) 0 3 = b63_root_ten_matrix 0 3 := by
  b63_root_ten_calc

set_option maxHeartbeats 400000 in
theorem b63_root_ten_entry_1_0 :
    b4b_toMatrix (b4b_root 10) 1 0 = b63_root_ten_matrix 1 0 := by
  b63_root_ten_calc

set_option maxHeartbeats 400000 in
theorem b63_root_ten_entry_1_1 :
    b4b_toMatrix (b4b_root 10) 1 1 = b63_root_ten_matrix 1 1 := by
  b63_root_ten_calc

set_option maxHeartbeats 400000 in
theorem b63_root_ten_entry_1_2 :
    b4b_toMatrix (b4b_root 10) 1 2 = b63_root_ten_matrix 1 2 := by
  b63_root_ten_calc

set_option maxHeartbeats 400000 in
theorem b63_root_ten_entry_1_3 :
    b4b_toMatrix (b4b_root 10) 1 3 = b63_root_ten_matrix 1 3 := by
  b63_root_ten_calc

set_option maxHeartbeats 400000 in
theorem b63_root_ten_entry_2_0 :
    b4b_toMatrix (b4b_root 10) 2 0 = b63_root_ten_matrix 2 0 := by
  b63_root_ten_calc

set_option maxHeartbeats 400000 in
theorem b63_root_ten_entry_2_1 :
    b4b_toMatrix (b4b_root 10) 2 1 = b63_root_ten_matrix 2 1 := by
  b63_root_ten_calc

set_option maxHeartbeats 400000 in
theorem b63_root_ten_entry_2_2 :
    b4b_toMatrix (b4b_root 10) 2 2 = b63_root_ten_matrix 2 2 := by
  b63_root_ten_calc

set_option maxHeartbeats 400000 in
theorem b63_root_ten_entry_2_3 :
    b4b_toMatrix (b4b_root 10) 2 3 = b63_root_ten_matrix 2 3 := by
  b63_root_ten_calc

set_option maxHeartbeats 400000 in
theorem b63_root_ten_entry_3_0 :
    b4b_toMatrix (b4b_root 10) 3 0 = b63_root_ten_matrix 3 0 := by
  b63_root_ten_calc

set_option maxHeartbeats 400000 in
theorem b63_root_ten_entry_3_1 :
    b4b_toMatrix (b4b_root 10) 3 1 = b63_root_ten_matrix 3 1 := by
  b63_root_ten_calc

set_option maxHeartbeats 400000 in
theorem b63_root_ten_entry_3_2 :
    b4b_toMatrix (b4b_root 10) 3 2 = b63_root_ten_matrix 3 2 := by
  b63_root_ten_calc

set_option maxHeartbeats 400000 in
theorem b63_root_ten_entry_3_3 :
    b4b_toMatrix (b4b_root 10) 3 3 = b63_root_ten_matrix 3 3 := by
  b63_root_ten_calc

theorem b63_root_ten_row_zero :
    b4b_toMatrix (b4b_root 10) 0 = b63_root_ten_matrix 0 := by
  funext j
  fin_cases j
  · exact b63_root_ten_entry_0_0
  · exact b63_root_ten_entry_0_1
  · exact b63_root_ten_entry_0_2
  · exact b63_root_ten_entry_0_3

theorem b63_root_ten_row_one :
    b4b_toMatrix (b4b_root 10) 1 = b63_root_ten_matrix 1 := by
  funext j
  fin_cases j
  · exact b63_root_ten_entry_1_0
  · exact b63_root_ten_entry_1_1
  · exact b63_root_ten_entry_1_2
  · exact b63_root_ten_entry_1_3

theorem b63_root_ten_row_two :
    b4b_toMatrix (b4b_root 10) 2 = b63_root_ten_matrix 2 := by
  funext j
  fin_cases j
  · exact b63_root_ten_entry_2_0
  · exact b63_root_ten_entry_2_1
  · exact b63_root_ten_entry_2_2
  · exact b63_root_ten_entry_2_3

theorem b63_root_ten_row_three :
    b4b_toMatrix (b4b_root 10) 3 = b63_root_ten_matrix 3 := by
  funext j
  fin_cases j
  · exact b63_root_ten_entry_3_0
  · exact b63_root_ten_entry_3_1
  · exact b63_root_ten_entry_3_2
  · exact b63_root_ten_entry_3_3

theorem b63_root_ten_matrix_eq :
    b4b_toMatrix (b4b_root 10) = b63_root_ten_matrix := by
  funext i
  fin_cases i
  · exact b63_root_ten_row_zero
  · exact b63_root_ten_row_one
  · exact b63_root_ten_row_two
  · exact b63_root_ten_row_three

set_option maxHeartbeats 400000 in
theorem b63_root_eleven_entry_0_0 :
    b4b_toMatrix (b4b_root 11) 0 0 = b63_root_eleven_matrix 0 0 := by
  b63_root_eleven_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eleven_entry_0_1 :
    b4b_toMatrix (b4b_root 11) 0 1 = b63_root_eleven_matrix 0 1 := by
  b63_root_eleven_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eleven_entry_0_2 :
    b4b_toMatrix (b4b_root 11) 0 2 = b63_root_eleven_matrix 0 2 := by
  b63_root_eleven_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eleven_entry_0_3 :
    b4b_toMatrix (b4b_root 11) 0 3 = b63_root_eleven_matrix 0 3 := by
  b63_root_eleven_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eleven_entry_1_0 :
    b4b_toMatrix (b4b_root 11) 1 0 = b63_root_eleven_matrix 1 0 := by
  b63_root_eleven_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eleven_entry_1_1 :
    b4b_toMatrix (b4b_root 11) 1 1 = b63_root_eleven_matrix 1 1 := by
  b63_root_eleven_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eleven_entry_1_2 :
    b4b_toMatrix (b4b_root 11) 1 2 = b63_root_eleven_matrix 1 2 := by
  b63_root_eleven_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eleven_entry_1_3 :
    b4b_toMatrix (b4b_root 11) 1 3 = b63_root_eleven_matrix 1 3 := by
  b63_root_eleven_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eleven_entry_2_0 :
    b4b_toMatrix (b4b_root 11) 2 0 = b63_root_eleven_matrix 2 0 := by
  b63_root_eleven_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eleven_entry_2_1 :
    b4b_toMatrix (b4b_root 11) 2 1 = b63_root_eleven_matrix 2 1 := by
  b63_root_eleven_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eleven_entry_2_2 :
    b4b_toMatrix (b4b_root 11) 2 2 = b63_root_eleven_matrix 2 2 := by
  b63_root_eleven_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eleven_entry_2_3 :
    b4b_toMatrix (b4b_root 11) 2 3 = b63_root_eleven_matrix 2 3 := by
  b63_root_eleven_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eleven_entry_3_0 :
    b4b_toMatrix (b4b_root 11) 3 0 = b63_root_eleven_matrix 3 0 := by
  b63_root_eleven_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eleven_entry_3_1 :
    b4b_toMatrix (b4b_root 11) 3 1 = b63_root_eleven_matrix 3 1 := by
  b63_root_eleven_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eleven_entry_3_2 :
    b4b_toMatrix (b4b_root 11) 3 2 = b63_root_eleven_matrix 3 2 := by
  b63_root_eleven_calc

set_option maxHeartbeats 400000 in
theorem b63_root_eleven_entry_3_3 :
    b4b_toMatrix (b4b_root 11) 3 3 = b63_root_eleven_matrix 3 3 := by
  b63_root_eleven_calc

theorem b63_root_eleven_row_zero :
    b4b_toMatrix (b4b_root 11) 0 = b63_root_eleven_matrix 0 := by
  funext j
  fin_cases j
  · exact b63_root_eleven_entry_0_0
  · exact b63_root_eleven_entry_0_1
  · exact b63_root_eleven_entry_0_2
  · exact b63_root_eleven_entry_0_3

theorem b63_root_eleven_row_one :
    b4b_toMatrix (b4b_root 11) 1 = b63_root_eleven_matrix 1 := by
  funext j
  fin_cases j
  · exact b63_root_eleven_entry_1_0
  · exact b63_root_eleven_entry_1_1
  · exact b63_root_eleven_entry_1_2
  · exact b63_root_eleven_entry_1_3

theorem b63_root_eleven_row_two :
    b4b_toMatrix (b4b_root 11) 2 = b63_root_eleven_matrix 2 := by
  funext j
  fin_cases j
  · exact b63_root_eleven_entry_2_0
  · exact b63_root_eleven_entry_2_1
  · exact b63_root_eleven_entry_2_2
  · exact b63_root_eleven_entry_2_3

theorem b63_root_eleven_row_three :
    b4b_toMatrix (b4b_root 11) 3 = b63_root_eleven_matrix 3 := by
  funext j
  fin_cases j
  · exact b63_root_eleven_entry_3_0
  · exact b63_root_eleven_entry_3_1
  · exact b63_root_eleven_entry_3_2
  · exact b63_root_eleven_entry_3_3

theorem b63_root_eleven_matrix_eq :
    b4b_toMatrix (b4b_root 11) = b63_root_eleven_matrix := by
  funext i
  fin_cases i
  · exact b63_root_eleven_row_zero
  · exact b63_root_eleven_row_one
  · exact b63_root_eleven_row_two
  · exact b63_root_eleven_row_three

set_option maxHeartbeats 400000 in
theorem b63_tail_group_eq : b63_tail_lhs = (b4b_generators 2) ^ 2 := by
  apply Subtype.ext
  change b4b_toMatrix b63_tail_lhs = b4b_toMatrix ((b4b_generators 2) ^ 2)
  simp only [b63_tail_lhs, map_mul, map_pow]
  rw [b63_root_eight_matrix_eq, b63_root_nine_matrix_eq,
    b63_root_ten_matrix_eq, b63_root_eleven_matrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b63_root_eight_matrix, b63_root_nine_matrix, b63_root_ten_matrix,
      b63_root_eleven_matrix, b4b_generators, b4b_toMatrix, pow_two, g32X, Matrix.mul_apply,
      Fin.sum_univ_four] <;>
    all_goals (try papers3b_omega_ring
      (papers3b_omega_pow g32h_omega g32h_omega_sq_add))

theorem b63_tail_list_eq :
    ((List.ofFn b4b_root).drop 8 |>.take 4).prod = b63_tail_lhs := by
  simp [b63_tail_lhs]
  group

def b63_class_swap_word : b4b_Group :=
  b4b_generators 0 * (b4b_generators 1) ^ 2

theorem b63_class_swap_inv : b63_class_swap_word⁻¹ =
    b4b_generators 1 * (b4b_generators 0) ^ 2 := by
  simp [b63_class_swap_word, b63_generator_zero_inv, b63_generator_one_inv]
  calc
    (b4b_generators 1) ^ (-2 : ℤ) = (b4b_generators 1) ^ (-2 : ℤ) *
        (b4b_generators 1) ^ 3 := by rw [b63_generator_one_cube, mul_one]
    _ = b4b_generators 1 := by group


local macro "b63_class_swap_calc" : tactic =>
  `(tactic| (rw [b63_class_swap_inv, b63_generator_one_inv] <;>
    simp [b63_class_swap_word, b4b_generators, b63_generator_zero_inv,
      b63_generator_one_inv, b63_class_swap_inv, b4b_toMatrix, pow_two, g32R1, g32R2,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_four] <;>
    ring_nf <;>
    all_goals (try simp only [b63_omega_seven, b63_omega_eight, b63_omega_nine,
      b63_omega_ten, b63_omega_eleven, b63_omega_twelve,
      (papers3b_omega_pow g32h_omega g32h_omega_sq_add).1,
      (papers3b_omega_pow g32h_omega g32h_omega_sq_add).2.1,
      (papers3b_omega_pow g32h_omega g32h_omega_sq_add).2.2.1,
      (papers3b_omega_pow g32h_omega g32h_omega_sq_add).2.2.2.1,
      (papers3b_omega_pow g32h_omega g32h_omega_sq_add).2.2.2.2]) <;>
    all_goals ring_nf))

set_option maxHeartbeats 400000 in
theorem b63_class_swap_entry_0_0 :
    b4b_toMatrix (b63_class_swap_word * b4b_generators 0 * b63_class_swap_word⁻¹) 0 0 =
      b4b_toMatrix ((b4b_generators 1)⁻¹) 0 0 := by
  b63_class_swap_calc

set_option maxHeartbeats 400000 in
theorem b63_class_swap_entry_0_1 :
    b4b_toMatrix (b63_class_swap_word * b4b_generators 0 * b63_class_swap_word⁻¹) 0 1 =
      b4b_toMatrix ((b4b_generators 1)⁻¹) 0 1 := by
  b63_class_swap_calc

set_option maxHeartbeats 400000 in
theorem b63_class_swap_entry_0_2 :
    b4b_toMatrix (b63_class_swap_word * b4b_generators 0 * b63_class_swap_word⁻¹) 0 2 =
      b4b_toMatrix ((b4b_generators 1)⁻¹) 0 2 := by
  b63_class_swap_calc

set_option maxHeartbeats 400000 in
theorem b63_class_swap_entry_0_3 :
    b4b_toMatrix (b63_class_swap_word * b4b_generators 0 * b63_class_swap_word⁻¹) 0 3 =
      b4b_toMatrix ((b4b_generators 1)⁻¹) 0 3 := by
  b63_class_swap_calc

set_option maxHeartbeats 400000 in
theorem b63_class_swap_entry_1_0 :
    b4b_toMatrix (b63_class_swap_word * b4b_generators 0 * b63_class_swap_word⁻¹) 1 0 =
      b4b_toMatrix ((b4b_generators 1)⁻¹) 1 0 := by
  b63_class_swap_calc

set_option maxHeartbeats 400000 in
theorem b63_class_swap_entry_1_1 :
    b4b_toMatrix (b63_class_swap_word * b4b_generators 0 * b63_class_swap_word⁻¹) 1 1 =
      b4b_toMatrix ((b4b_generators 1)⁻¹) 1 1 := by
  b63_class_swap_calc

set_option maxHeartbeats 400000 in
theorem b63_class_swap_entry_1_2 :
    b4b_toMatrix (b63_class_swap_word * b4b_generators 0 * b63_class_swap_word⁻¹) 1 2 =
      b4b_toMatrix ((b4b_generators 1)⁻¹) 1 2 := by
  b63_class_swap_calc

set_option maxHeartbeats 400000 in
theorem b63_class_swap_entry_1_3 :
    b4b_toMatrix (b63_class_swap_word * b4b_generators 0 * b63_class_swap_word⁻¹) 1 3 =
      b4b_toMatrix ((b4b_generators 1)⁻¹) 1 3 := by
  b63_class_swap_calc

set_option maxHeartbeats 400000 in
theorem b63_class_swap_entry_2_0 :
    b4b_toMatrix (b63_class_swap_word * b4b_generators 0 * b63_class_swap_word⁻¹) 2 0 =
      b4b_toMatrix ((b4b_generators 1)⁻¹) 2 0 := by
  b63_class_swap_calc

set_option maxHeartbeats 400000 in
theorem b63_class_swap_entry_2_1 :
    b4b_toMatrix (b63_class_swap_word * b4b_generators 0 * b63_class_swap_word⁻¹) 2 1 =
      b4b_toMatrix ((b4b_generators 1)⁻¹) 2 1 := by
  b63_class_swap_calc

set_option maxHeartbeats 400000 in
theorem b63_class_swap_entry_2_2 :
    b4b_toMatrix (b63_class_swap_word * b4b_generators 0 * b63_class_swap_word⁻¹) 2 2 =
      b4b_toMatrix ((b4b_generators 1)⁻¹) 2 2 := by
  b63_class_swap_calc

set_option maxHeartbeats 400000 in
theorem b63_class_swap_entry_2_3 :
    b4b_toMatrix (b63_class_swap_word * b4b_generators 0 * b63_class_swap_word⁻¹) 2 3 =
      b4b_toMatrix ((b4b_generators 1)⁻¹) 2 3 := by
  b63_class_swap_calc

set_option maxHeartbeats 400000 in
theorem b63_class_swap_entry_3_0 :
    b4b_toMatrix (b63_class_swap_word * b4b_generators 0 * b63_class_swap_word⁻¹) 3 0 =
      b4b_toMatrix ((b4b_generators 1)⁻¹) 3 0 := by
  b63_class_swap_calc

set_option maxHeartbeats 400000 in
theorem b63_class_swap_entry_3_1 :
    b4b_toMatrix (b63_class_swap_word * b4b_generators 0 * b63_class_swap_word⁻¹) 3 1 =
      b4b_toMatrix ((b4b_generators 1)⁻¹) 3 1 := by
  b63_class_swap_calc

set_option maxHeartbeats 400000 in
theorem b63_class_swap_entry_3_2 :
    b4b_toMatrix (b63_class_swap_word * b4b_generators 0 * b63_class_swap_word⁻¹) 3 2 =
      b4b_toMatrix ((b4b_generators 1)⁻¹) 3 2 := by
  b63_class_swap_calc

set_option maxHeartbeats 400000 in
theorem b63_class_swap_entry_3_3 :
    b4b_toMatrix (b63_class_swap_word * b4b_generators 0 * b63_class_swap_word⁻¹) 3 3 =
      b4b_toMatrix ((b4b_generators 1)⁻¹) 3 3 := by
  b63_class_swap_calc

theorem b63_class_swap_row_zero :
    b4b_toMatrix (b63_class_swap_word * b4b_generators 0 * b63_class_swap_word⁻¹) 0 =
      b4b_toMatrix ((b4b_generators 1)⁻¹) 0 := by
  funext j
  fin_cases j
  · exact b63_class_swap_entry_0_0
  · exact b63_class_swap_entry_0_1
  · exact b63_class_swap_entry_0_2
  · exact b63_class_swap_entry_0_3

theorem b63_class_swap_row_one :
    b4b_toMatrix (b63_class_swap_word * b4b_generators 0 * b63_class_swap_word⁻¹) 1 =
      b4b_toMatrix ((b4b_generators 1)⁻¹) 1 := by
  funext j
  fin_cases j
  · exact b63_class_swap_entry_1_0
  · exact b63_class_swap_entry_1_1
  · exact b63_class_swap_entry_1_2
  · exact b63_class_swap_entry_1_3

theorem b63_class_swap_row_two :
    b4b_toMatrix (b63_class_swap_word * b4b_generators 0 * b63_class_swap_word⁻¹) 2 =
      b4b_toMatrix ((b4b_generators 1)⁻¹) 2 := by
  funext j
  fin_cases j
  · exact b63_class_swap_entry_2_0
  · exact b63_class_swap_entry_2_1
  · exact b63_class_swap_entry_2_2
  · exact b63_class_swap_entry_2_3

theorem b63_class_swap_row_three :
    b4b_toMatrix (b63_class_swap_word * b4b_generators 0 * b63_class_swap_word⁻¹) 3 =
      b4b_toMatrix ((b4b_generators 1)⁻¹) 3 := by
  funext j
  fin_cases j
  · exact b63_class_swap_entry_3_0
  · exact b63_class_swap_entry_3_1
  · exact b63_class_swap_entry_3_2
  · exact b63_class_swap_entry_3_3

theorem b63_class_swap_eq :
    b63_class_swap_word * b4b_generators 0 * b63_class_swap_word⁻¹ =
      (b4b_generators 1)⁻¹ := by
  apply Subtype.ext
  funext i
  fin_cases i
  · exact b63_class_swap_row_zero
  · exact b63_class_swap_row_one
  · exact b63_class_swap_row_two
  · exact b63_class_swap_row_three

theorem b63_class_swap_inverse_eq :
    b63_class_swap_word * (b4b_generators 0)⁻¹ * b63_class_swap_word⁻¹ =
      b4b_generators 1 := by
  have h := congrArg Inv.inv b63_class_swap_eq
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using h

def b63_root_four_word : b4b_Group :=
  b4b_generators 2 * b4b_generators 0 * (b4b_generators 2) ^ 3

theorem b63_root_four_expansion : b4b_root 4 = b63_root_four_word := by
  simp [b63_root_four_word, b4b_root, b4b_reflection, b63_generator_two_inv]

def b63_root_six_word : b4b_Group :=
  b4b_generators 3 * b4b_generators 0 * (b4b_generators 3) ^ 2

theorem b63_root_six_expansion : b4b_root 6 = b63_root_six_word := by
  simp [b63_root_six_word, b4b_root, b4b_reflection, b63_generator_three_inv]

def b63_root_four_matrix : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(2 + g32h_omega) / 3, (1 + 2 * g32h_omega) / 3, 0,
       (2 + g32h_omega) / 3;
     (-2 - g32h_omega) / 3, (2 + g32h_omega) / 3, 0,
       (1 + 2 * g32h_omega) / 3;
     0, 0, 1, 0;
     (-1 - 2 * g32h_omega) / 3, (-2 - g32h_omega) / 3, 0,
       (2 + g32h_omega) / 3]

def b63_root_six_matrix : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(2 + g32h_omega) / 3, 0, (1 - g32h_omega) / 3,
       (-2 - g32h_omega) / 3;
     0, 1, 0, 0;
     (1 - g32h_omega) / 3, 0, (2 + g32h_omega) / 3,
       (2 + g32h_omega) / 3;
     (1 + 2 * g32h_omega) / 3, 0, (-1 - 2 * g32h_omega) / 3,
       (2 + g32h_omega) / 3]

local macro "b63_root_four_calc" : tactic =>
  `(tactic| (rw [b63_root_four_expansion] <;>
    simp [b63_root_four_word, b63_root_four_matrix, b4b_generators, b4b_toMatrix,
      pow_two, pow_three, g32R1, g32X, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_four] <;>
    b63_reduce_omega))

local macro "b63_root_six_calc" : tactic =>
  `(tactic| (rw [b63_root_six_expansion] <;>
    simp [b63_root_six_word, b63_root_six_matrix, b4b_generators, b4b_toMatrix,
      pow_two, g32R1, g32Y, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_four] <;>
    b63_reduce_omega))

set_option maxHeartbeats 400000 in
theorem b63_root_four_entry_0_0 :
    b4b_toMatrix (b4b_root 4) 0 0 = b63_root_four_matrix 0 0 := by
  b63_root_four_calc

set_option maxHeartbeats 400000 in
theorem b63_root_four_entry_0_1 :
    b4b_toMatrix (b4b_root 4) 0 1 = b63_root_four_matrix 0 1 := by
  b63_root_four_calc

set_option maxHeartbeats 400000 in
theorem b63_root_four_entry_0_2 :
    b4b_toMatrix (b4b_root 4) 0 2 = b63_root_four_matrix 0 2 := by
  b63_root_four_calc

set_option maxHeartbeats 400000 in
theorem b63_root_four_entry_0_3 :
    b4b_toMatrix (b4b_root 4) 0 3 = b63_root_four_matrix 0 3 := by
  b63_root_four_calc

set_option maxHeartbeats 400000 in
theorem b63_root_four_entry_1_0 :
    b4b_toMatrix (b4b_root 4) 1 0 = b63_root_four_matrix 1 0 := by
  b63_root_four_calc

set_option maxHeartbeats 400000 in
theorem b63_root_four_entry_1_1 :
    b4b_toMatrix (b4b_root 4) 1 1 = b63_root_four_matrix 1 1 := by
  b63_root_four_calc

set_option maxHeartbeats 400000 in
theorem b63_root_four_entry_1_2 :
    b4b_toMatrix (b4b_root 4) 1 2 = b63_root_four_matrix 1 2 := by
  b63_root_four_calc

set_option maxHeartbeats 400000 in
theorem b63_root_four_entry_1_3 :
    b4b_toMatrix (b4b_root 4) 1 3 = b63_root_four_matrix 1 3 := by
  b63_root_four_calc

set_option maxHeartbeats 400000 in
theorem b63_root_four_entry_2_0 :
    b4b_toMatrix (b4b_root 4) 2 0 = b63_root_four_matrix 2 0 := by
  b63_root_four_calc

set_option maxHeartbeats 400000 in
theorem b63_root_four_entry_2_1 :
    b4b_toMatrix (b4b_root 4) 2 1 = b63_root_four_matrix 2 1 := by
  b63_root_four_calc

set_option maxHeartbeats 400000 in
theorem b63_root_four_entry_2_2 :
    b4b_toMatrix (b4b_root 4) 2 2 = b63_root_four_matrix 2 2 := by
  b63_root_four_calc

set_option maxHeartbeats 400000 in
theorem b63_root_four_entry_2_3 :
    b4b_toMatrix (b4b_root 4) 2 3 = b63_root_four_matrix 2 3 := by
  b63_root_four_calc

set_option maxHeartbeats 400000 in
theorem b63_root_four_entry_3_0 :
    b4b_toMatrix (b4b_root 4) 3 0 = b63_root_four_matrix 3 0 := by
  b63_root_four_calc

set_option maxHeartbeats 400000 in
theorem b63_root_four_entry_3_1 :
    b4b_toMatrix (b4b_root 4) 3 1 = b63_root_four_matrix 3 1 := by
  b63_root_four_calc

set_option maxHeartbeats 400000 in
theorem b63_root_four_entry_3_2 :
    b4b_toMatrix (b4b_root 4) 3 2 = b63_root_four_matrix 3 2 := by
  b63_root_four_calc

set_option maxHeartbeats 400000 in
theorem b63_root_four_entry_3_3 :
    b4b_toMatrix (b4b_root 4) 3 3 = b63_root_four_matrix 3 3 := by
  b63_root_four_calc

theorem b63_root_four_row_zero :
    b4b_toMatrix (b4b_root 4) 0 = b63_root_four_matrix 0 := by
  funext j
  fin_cases j
  · exact b63_root_four_entry_0_0
  · exact b63_root_four_entry_0_1
  · exact b63_root_four_entry_0_2
  · exact b63_root_four_entry_0_3

theorem b63_root_four_row_one :
    b4b_toMatrix (b4b_root 4) 1 = b63_root_four_matrix 1 := by
  funext j
  fin_cases j
  · exact b63_root_four_entry_1_0
  · exact b63_root_four_entry_1_1
  · exact b63_root_four_entry_1_2
  · exact b63_root_four_entry_1_3

theorem b63_root_four_row_two :
    b4b_toMatrix (b4b_root 4) 2 = b63_root_four_matrix 2 := by
  funext j
  fin_cases j
  · exact b63_root_four_entry_2_0
  · exact b63_root_four_entry_2_1
  · exact b63_root_four_entry_2_2
  · exact b63_root_four_entry_2_3

theorem b63_root_four_row_three :
    b4b_toMatrix (b4b_root 4) 3 = b63_root_four_matrix 3 := by
  funext j
  fin_cases j
  · exact b63_root_four_entry_3_0
  · exact b63_root_four_entry_3_1
  · exact b63_root_four_entry_3_2
  · exact b63_root_four_entry_3_3

theorem b63_root_four_matrix_eq :
    b4b_toMatrix (b4b_root 4) = b63_root_four_matrix := by
  funext i
  fin_cases i
  · exact b63_root_four_row_zero
  · exact b63_root_four_row_one
  · exact b63_root_four_row_two
  · exact b63_root_four_row_three

set_option maxHeartbeats 400000 in
theorem b63_root_six_entry_0_0 :
    b4b_toMatrix (b4b_root 6) 0 0 = b63_root_six_matrix 0 0 := by
  b63_root_six_calc

set_option maxHeartbeats 400000 in
theorem b63_root_six_entry_0_1 :
    b4b_toMatrix (b4b_root 6) 0 1 = b63_root_six_matrix 0 1 := by
  b63_root_six_calc

set_option maxHeartbeats 400000 in
theorem b63_root_six_entry_0_2 :
    b4b_toMatrix (b4b_root 6) 0 2 = b63_root_six_matrix 0 2 := by
  b63_root_six_calc

set_option maxHeartbeats 400000 in
theorem b63_root_six_entry_0_3 :
    b4b_toMatrix (b4b_root 6) 0 3 = b63_root_six_matrix 0 3 := by
  b63_root_six_calc

set_option maxHeartbeats 400000 in
theorem b63_root_six_entry_1_0 :
    b4b_toMatrix (b4b_root 6) 1 0 = b63_root_six_matrix 1 0 := by
  b63_root_six_calc

set_option maxHeartbeats 400000 in
theorem b63_root_six_entry_1_1 :
    b4b_toMatrix (b4b_root 6) 1 1 = b63_root_six_matrix 1 1 := by
  b63_root_six_calc

set_option maxHeartbeats 400000 in
theorem b63_root_six_entry_1_2 :
    b4b_toMatrix (b4b_root 6) 1 2 = b63_root_six_matrix 1 2 := by
  b63_root_six_calc

set_option maxHeartbeats 400000 in
theorem b63_root_six_entry_1_3 :
    b4b_toMatrix (b4b_root 6) 1 3 = b63_root_six_matrix 1 3 := by
  b63_root_six_calc

set_option maxHeartbeats 400000 in
theorem b63_root_six_entry_2_0 :
    b4b_toMatrix (b4b_root 6) 2 0 = b63_root_six_matrix 2 0 := by
  b63_root_six_calc

set_option maxHeartbeats 400000 in
theorem b63_root_six_entry_2_1 :
    b4b_toMatrix (b4b_root 6) 2 1 = b63_root_six_matrix 2 1 := by
  b63_root_six_calc

set_option maxHeartbeats 400000 in
theorem b63_root_six_entry_2_2 :
    b4b_toMatrix (b4b_root 6) 2 2 = b63_root_six_matrix 2 2 := by
  b63_root_six_calc

set_option maxHeartbeats 400000 in
theorem b63_root_six_entry_2_3 :
    b4b_toMatrix (b4b_root 6) 2 3 = b63_root_six_matrix 2 3 := by
  b63_root_six_calc

set_option maxHeartbeats 400000 in
theorem b63_root_six_entry_3_0 :
    b4b_toMatrix (b4b_root 6) 3 0 = b63_root_six_matrix 3 0 := by
  b63_root_six_calc

set_option maxHeartbeats 400000 in
theorem b63_root_six_entry_3_1 :
    b4b_toMatrix (b4b_root 6) 3 1 = b63_root_six_matrix 3 1 := by
  b63_root_six_calc

set_option maxHeartbeats 400000 in
theorem b63_root_six_entry_3_2 :
    b4b_toMatrix (b4b_root 6) 3 2 = b63_root_six_matrix 3 2 := by
  b63_root_six_calc

set_option maxHeartbeats 400000 in
theorem b63_root_six_entry_3_3 :
    b4b_toMatrix (b4b_root 6) 3 3 = b63_root_six_matrix 3 3 := by
  b63_root_six_calc

theorem b63_root_six_row_zero :
    b4b_toMatrix (b4b_root 6) 0 = b63_root_six_matrix 0 := by
  funext j
  fin_cases j
  · exact b63_root_six_entry_0_0
  · exact b63_root_six_entry_0_1
  · exact b63_root_six_entry_0_2
  · exact b63_root_six_entry_0_3

theorem b63_root_six_row_one :
    b4b_toMatrix (b4b_root 6) 1 = b63_root_six_matrix 1 := by
  funext j
  fin_cases j
  · exact b63_root_six_entry_1_0
  · exact b63_root_six_entry_1_1
  · exact b63_root_six_entry_1_2
  · exact b63_root_six_entry_1_3

theorem b63_root_six_row_two :
    b4b_toMatrix (b4b_root 6) 2 = b63_root_six_matrix 2 := by
  funext j
  fin_cases j
  · exact b63_root_six_entry_2_0
  · exact b63_root_six_entry_2_1
  · exact b63_root_six_entry_2_2
  · exact b63_root_six_entry_2_3

theorem b63_root_six_row_three :
    b4b_toMatrix (b4b_root 6) 3 = b63_root_six_matrix 3 := by
  funext j
  fin_cases j
  · exact b63_root_six_entry_3_0
  · exact b63_root_six_entry_3_1
  · exact b63_root_six_entry_3_2
  · exact b63_root_six_entry_3_3

theorem b63_root_six_matrix_eq :
    b4b_toMatrix (b4b_root 6) = b63_root_six_matrix := by
  funext i
  fin_cases i
  · exact b63_root_six_row_zero
  · exact b63_root_six_row_one
  · exact b63_root_six_row_two
  · exact b63_root_six_row_three

theorem b63_root_six_cube : (b4b_root 6) ^ 3 = 1 := by
  rw [b63_root_six_expansion]
  simp only [b63_root_six_word]
  rw [show (b4b_generators 3) ^ 2 = (b4b_generators 3)⁻¹ from
    b63_generator_three_inv.symm]
  calc
    (b4b_generators 3 * b4b_generators 0 * (b4b_generators 3)⁻¹) ^ 3 =
        b4b_generators 3 * (b4b_generators 0) ^ 3 * (b4b_generators 3)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    _ = 1 := by rw [b63_generator_zero_cube]; simp

theorem b63_root_seven_square : b4b_root 7 = (b4b_root 6) ^ 2 := by
  change (b4b_root 6)⁻¹ = (b4b_root 6) ^ 2
  calc
    (b4b_root 6)⁻¹ = (b4b_root 6)⁻¹ * 1 := by simp
    _ = (b4b_root 6)⁻¹ * (b4b_root 6) ^ 3 := by rw [b63_root_six_cube]
    _ = (b4b_root 6) ^ 2 := by group

def b63_generator_three_root_word : b4b_Group :=
  b4b_root 0 * b4b_root 2 * b4b_root 11 * b4b_root 2 * b4b_root 12 * b4b_root 6


local macro "b63_generator_three_word_calc" : tactic =>
  `(tactic| (rw [b63_generator_three_root_word,
      show b4b_root 0 = b4b_generators 0 from rfl,
      show b4b_root 2 = (b4b_generators 1)⁻¹ from rfl,
      show b4b_root 12 = (b4b_generators 2) ^ 2 from rfl,
      b63_generator_one_inv] <;>
    simp only [map_mul] <;>
    rw [b63_root_eleven_matrix_eq, b63_root_six_matrix_eq] <;>
    simp [b4b_generators, b4b_toMatrix, b63_root_eleven_matrix,
      b63_root_six_matrix, pow_two, g32R1, g32R2, g32X, g32Y,
      Matrix.mul_apply, Fin.sum_univ_four] <;> b63_reduce_omega))

set_option maxHeartbeats 400000 in
theorem b63_generator_three_word_entry_0_0 :
    b4b_toMatrix b63_generator_three_root_word 0 0 =
      b4b_toMatrix (b4b_generators 3) 0 0 := by
  b63_generator_three_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_three_word_entry_0_1 :
    b4b_toMatrix b63_generator_three_root_word 0 1 =
      b4b_toMatrix (b4b_generators 3) 0 1 := by
  b63_generator_three_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_three_word_entry_0_2 :
    b4b_toMatrix b63_generator_three_root_word 0 2 =
      b4b_toMatrix (b4b_generators 3) 0 2 := by
  b63_generator_three_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_three_word_entry_0_3 :
    b4b_toMatrix b63_generator_three_root_word 0 3 =
      b4b_toMatrix (b4b_generators 3) 0 3 := by
  b63_generator_three_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_three_word_entry_1_0 :
    b4b_toMatrix b63_generator_three_root_word 1 0 =
      b4b_toMatrix (b4b_generators 3) 1 0 := by
  b63_generator_three_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_three_word_entry_1_1 :
    b4b_toMatrix b63_generator_three_root_word 1 1 =
      b4b_toMatrix (b4b_generators 3) 1 1 := by
  b63_generator_three_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_three_word_entry_1_2 :
    b4b_toMatrix b63_generator_three_root_word 1 2 =
      b4b_toMatrix (b4b_generators 3) 1 2 := by
  b63_generator_three_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_three_word_entry_1_3 :
    b4b_toMatrix b63_generator_three_root_word 1 3 =
      b4b_toMatrix (b4b_generators 3) 1 3 := by
  b63_generator_three_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_three_word_entry_2_0 :
    b4b_toMatrix b63_generator_three_root_word 2 0 =
      b4b_toMatrix (b4b_generators 3) 2 0 := by
  b63_generator_three_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_three_word_entry_2_1 :
    b4b_toMatrix b63_generator_three_root_word 2 1 =
      b4b_toMatrix (b4b_generators 3) 2 1 := by
  b63_generator_three_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_three_word_entry_2_2 :
    b4b_toMatrix b63_generator_three_root_word 2 2 =
      b4b_toMatrix (b4b_generators 3) 2 2 := by
  b63_generator_three_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_three_word_entry_2_3 :
    b4b_toMatrix b63_generator_three_root_word 2 3 =
      b4b_toMatrix (b4b_generators 3) 2 3 := by
  b63_generator_three_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_three_word_entry_3_0 :
    b4b_toMatrix b63_generator_three_root_word 3 0 =
      b4b_toMatrix (b4b_generators 3) 3 0 := by
  b63_generator_three_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_three_word_entry_3_1 :
    b4b_toMatrix b63_generator_three_root_word 3 1 =
      b4b_toMatrix (b4b_generators 3) 3 1 := by
  b63_generator_three_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_three_word_entry_3_2 :
    b4b_toMatrix b63_generator_three_root_word 3 2 =
      b4b_toMatrix (b4b_generators 3) 3 2 := by
  b63_generator_three_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_three_word_entry_3_3 :
    b4b_toMatrix b63_generator_three_root_word 3 3 =
      b4b_toMatrix (b4b_generators 3) 3 3 := by
  b63_generator_three_word_calc

theorem b63_generator_three_word_row_zero :
    b4b_toMatrix b63_generator_three_root_word 0 =
      b4b_toMatrix (b4b_generators 3) 0 := by
  funext j
  fin_cases j
  · exact b63_generator_three_word_entry_0_0
  · exact b63_generator_three_word_entry_0_1
  · exact b63_generator_three_word_entry_0_2
  · exact b63_generator_three_word_entry_0_3

theorem b63_generator_three_word_row_one :
    b4b_toMatrix b63_generator_three_root_word 1 =
      b4b_toMatrix (b4b_generators 3) 1 := by
  funext j
  fin_cases j
  · exact b63_generator_three_word_entry_1_0
  · exact b63_generator_three_word_entry_1_1
  · exact b63_generator_three_word_entry_1_2
  · exact b63_generator_three_word_entry_1_3

theorem b63_generator_three_word_row_two :
    b4b_toMatrix b63_generator_three_root_word 2 =
      b4b_toMatrix (b4b_generators 3) 2 := by
  funext j
  fin_cases j
  · exact b63_generator_three_word_entry_2_0
  · exact b63_generator_three_word_entry_2_1
  · exact b63_generator_three_word_entry_2_2
  · exact b63_generator_three_word_entry_2_3

theorem b63_generator_three_word_row_three :
    b4b_toMatrix b63_generator_three_root_word 3 =
      b4b_toMatrix (b4b_generators 3) 3 := by
  funext j
  fin_cases j
  · exact b63_generator_three_word_entry_3_0
  · exact b63_generator_three_word_entry_3_1
  · exact b63_generator_three_word_entry_3_2
  · exact b63_generator_three_word_entry_3_3

theorem b63_generator_three_root_word_eq :
    b63_generator_three_root_word = b4b_generators 3 := by
  apply Subtype.ext
  funext i
  fin_cases i
  · exact b63_generator_three_word_row_zero
  · exact b63_generator_three_word_row_one
  · exact b63_generator_three_word_row_two
  · exact b63_generator_three_word_row_three

def b63_generator_two_root_word : b4b_Group :=
  b4b_root 0 * b4b_root 4 * b4b_root 7 * b4b_root 8 *
    b4b_root 3 * b4b_root 12 * b4b_root 2 * b4b_root 6

local macro "b63_generator_two_word_calc" : tactic =>
  `(tactic| (rw [b63_generator_two_root_word,
      show b4b_root 0 = b4b_generators 0 from rfl,
      show b4b_root 3 = b4b_generators 1 from rfl,
      show b4b_root 12 = (b4b_generators 2) ^ 2 from rfl,
      show b4b_root 2 = (b4b_generators 1)⁻¹ from rfl,
      b63_root_seven_square, b63_generator_one_inv] <;>
    simp only [map_mul, map_pow] <;>
    rw [b63_root_four_matrix_eq, b63_root_six_matrix_eq,
      b63_root_eight_matrix_eq] <;>
    simp [b4b_generators, b4b_toMatrix, b63_root_four_matrix,
      b63_root_six_matrix, b63_root_eight_matrix, pow_two,
      g32R1, g32R2, g32X, Matrix.mul_apply, Fin.sum_univ_four] <;>
    b63_reduce_omega))

set_option maxHeartbeats 400000 in
theorem b63_generator_two_word_entry_0_0 :
    b4b_toMatrix b63_generator_two_root_word 0 0 =
      b4b_toMatrix (b4b_generators 2) 0 0 := by
  b63_generator_two_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_two_word_entry_0_1 :
    b4b_toMatrix b63_generator_two_root_word 0 1 =
      b4b_toMatrix (b4b_generators 2) 0 1 := by
  b63_generator_two_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_two_word_entry_0_2 :
    b4b_toMatrix b63_generator_two_root_word 0 2 =
      b4b_toMatrix (b4b_generators 2) 0 2 := by
  b63_generator_two_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_two_word_entry_0_3 :
    b4b_toMatrix b63_generator_two_root_word 0 3 =
      b4b_toMatrix (b4b_generators 2) 0 3 := by
  b63_generator_two_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_two_word_entry_1_0 :
    b4b_toMatrix b63_generator_two_root_word 1 0 =
      b4b_toMatrix (b4b_generators 2) 1 0 := by
  b63_generator_two_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_two_word_entry_1_1 :
    b4b_toMatrix b63_generator_two_root_word 1 1 =
      b4b_toMatrix (b4b_generators 2) 1 1 := by
  b63_generator_two_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_two_word_entry_1_2 :
    b4b_toMatrix b63_generator_two_root_word 1 2 =
      b4b_toMatrix (b4b_generators 2) 1 2 := by
  b63_generator_two_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_two_word_entry_1_3 :
    b4b_toMatrix b63_generator_two_root_word 1 3 =
      b4b_toMatrix (b4b_generators 2) 1 3 := by
  b63_generator_two_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_two_word_entry_2_0 :
    b4b_toMatrix b63_generator_two_root_word 2 0 =
      b4b_toMatrix (b4b_generators 2) 2 0 := by
  b63_generator_two_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_two_word_entry_2_1 :
    b4b_toMatrix b63_generator_two_root_word 2 1 =
      b4b_toMatrix (b4b_generators 2) 2 1 := by
  b63_generator_two_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_two_word_entry_2_2 :
    b4b_toMatrix b63_generator_two_root_word 2 2 =
      b4b_toMatrix (b4b_generators 2) 2 2 := by
  b63_generator_two_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_two_word_entry_2_3 :
    b4b_toMatrix b63_generator_two_root_word 2 3 =
      b4b_toMatrix (b4b_generators 2) 2 3 := by
  b63_generator_two_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_two_word_entry_3_0 :
    b4b_toMatrix b63_generator_two_root_word 3 0 =
      b4b_toMatrix (b4b_generators 2) 3 0 := by
  b63_generator_two_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_two_word_entry_3_1 :
    b4b_toMatrix b63_generator_two_root_word 3 1 =
      b4b_toMatrix (b4b_generators 2) 3 1 := by
  b63_generator_two_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_two_word_entry_3_2 :
    b4b_toMatrix b63_generator_two_root_word 3 2 =
      b4b_toMatrix (b4b_generators 2) 3 2 := by
  b63_generator_two_word_calc

set_option maxHeartbeats 400000 in
theorem b63_generator_two_word_entry_3_3 :
    b4b_toMatrix b63_generator_two_root_word 3 3 =
      b4b_toMatrix (b4b_generators 2) 3 3 := by
  b63_generator_two_word_calc

theorem b63_generator_two_word_row_zero :
    b4b_toMatrix b63_generator_two_root_word 0 =
      b4b_toMatrix (b4b_generators 2) 0 := by
  funext j
  fin_cases j
  · exact b63_generator_two_word_entry_0_0
  · exact b63_generator_two_word_entry_0_1
  · exact b63_generator_two_word_entry_0_2
  · exact b63_generator_two_word_entry_0_3

theorem b63_generator_two_word_row_one :
    b4b_toMatrix b63_generator_two_root_word 1 =
      b4b_toMatrix (b4b_generators 2) 1 := by
  funext j
  fin_cases j
  · exact b63_generator_two_word_entry_1_0
  · exact b63_generator_two_word_entry_1_1
  · exact b63_generator_two_word_entry_1_2
  · exact b63_generator_two_word_entry_1_3

theorem b63_generator_two_word_row_two :
    b4b_toMatrix b63_generator_two_root_word 2 =
      b4b_toMatrix (b4b_generators 2) 2 := by
  funext j
  fin_cases j
  · exact b63_generator_two_word_entry_2_0
  · exact b63_generator_two_word_entry_2_1
  · exact b63_generator_two_word_entry_2_2
  · exact b63_generator_two_word_entry_2_3

theorem b63_generator_two_word_row_three :
    b4b_toMatrix b63_generator_two_root_word 3 =
      b4b_toMatrix (b4b_generators 2) 3 := by
  funext j
  fin_cases j
  · exact b63_generator_two_word_entry_3_0
  · exact b63_generator_two_word_entry_3_1
  · exact b63_generator_two_word_entry_3_2
  · exact b63_generator_two_word_entry_3_3

theorem b63_generator_two_root_word_eq :
    b63_generator_two_root_word = b4b_generators 2 := by
  apply Subtype.ext
  funext i
  fin_cases i
  · exact b63_generator_two_word_row_zero
  · exact b63_generator_two_word_row_one
  · exact b63_generator_two_word_row_two
  · exact b63_generator_two_word_row_three


end HodgeLean.Foundations.Program
