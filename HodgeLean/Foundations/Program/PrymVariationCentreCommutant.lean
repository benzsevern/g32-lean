import HodgeLean.Foundations.Program.PrymVariationCentreRepresentation

set_option maxHeartbeats 400000
set_option maxRecDepth 2048
noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem b63d_matrix_commutant (P : Matrix (Fin 4) (Fin 4) ℂ)
    (h1 : P * g32R1 g32h_omega = g32R1 g32h_omega * P)
    (h2 : P * g32R2 g32h_omega = g32R2 g32h_omega * P)
    (hX : P * g32X g32h_omega = g32X g32h_omega * P) :
    P = P 0 0 • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have e0 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 0 0) h1
  norm_num [Matrix.mul_apply, g32R1, Fin.sum_univ_four] at e0
  have e1 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 0 1) h1
  norm_num [Matrix.mul_apply, g32R1, Fin.sum_univ_four] at e1
  have e2 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 0 2) h1
  norm_num [Matrix.mul_apply, g32R1, Fin.sum_univ_four] at e2
  have e3 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 0 3) h1
  norm_num [Matrix.mul_apply, g32R1, Fin.sum_univ_four] at e3
  have e4 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 1 0) h1
  norm_num [Matrix.mul_apply, g32R1, Fin.sum_univ_four] at e4
  have e8 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 2 0) h1
  norm_num [Matrix.mul_apply, g32R1, Fin.sum_univ_four] at e8
  have e16 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 0 0) h2
  norm_num [Matrix.mul_apply, g32R2, Fin.sum_univ_four] at e16
  have e17 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 0 1) h2
  norm_num [Matrix.mul_apply, g32R2, Fin.sum_univ_four] at e17
  have e18 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 0 2) h2
  norm_num [Matrix.mul_apply, g32R2, Fin.sum_univ_four] at e18
  have e19 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 0 3) h2
  norm_num [Matrix.mul_apply, g32R2, Fin.sum_univ_four] at e19
  have e20 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 1 0) h2
  norm_num [Matrix.mul_apply, g32R2, Fin.sum_univ_four] at e20
  have e33 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 0 1) hX
  norm_num [Matrix.mul_apply, g32X, Fin.sum_univ_four] at e33
  have e35 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 0 3) hX
  norm_num [Matrix.mul_apply, g32X, Fin.sum_univ_four] at e35
  have e36 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 1 0) hX
  norm_num [Matrix.mul_apply, g32X, Fin.sum_univ_four] at e36
  have e37 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 1 1) hX
  norm_num [Matrix.mul_apply, g32X, Fin.sum_univ_four] at e37
  have p1 : P 0 1 = 0 := by
    linear_combination ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e0 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * g32h_omega) * e4 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * g32h_omega) * e8 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e16 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e17 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e19 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * g32h_omega) * e33 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e35 + - ((-1 / 3 : ℂ) * (P 0 1) + (1 / 3 : ℂ) * (P 0 2)) * g32h_omega_sq_add
  have p2 : P 0 2 = 0 := by
    linear_combination ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * g32h_omega) * e0 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e4 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e8 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * g32h_omega) * e16 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e17 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e19 + (0 + -1 * g32h_omega) * e33 + - ((1 / 3 : ℂ) * (P 0 0) + (1 / 3 : ℂ) * (P 0 1) + (-2 / 3 : ℂ) * (P 0 2) + (-1 / 3 : ℂ) * (P 1 1) + (1 / 3 : ℂ) * (P 1 3) + (-1 / 3 : ℂ) * (P 2 0) + (-1 / 3 : ℂ) * (P 2 1) + (1 / 3 : ℂ) * (P 2 3) + (-1 / 3 : ℂ) * (P 3 0)) * g32h_omega_sq_add
  have p3 : P 0 3 = 0 := by
    linear_combination ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e33 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e35 + - ((-1 / 3 : ℂ) * (P 0 3)) * g32h_omega_sq_add
  have p4 : P 1 0 = 0 := by
    linear_combination ((1 / 3 : ℂ) + (2 / 3 : ℂ) * g32h_omega) * e0 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e4 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e8 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e16 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * g32h_omega) * e17 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * g32h_omega) * e19 + -1 * e36 + - ((1 / 3 : ℂ) * (P 0 0) + (-1 / 3 : ℂ) * (P 0 1) + (-1 / 3 : ℂ) * (P 0 2) + (-2 / 3 : ℂ) * (P 1 0) + (-1 / 3 : ℂ) * (P 1 1) + (1 / 3 : ℂ) * (P 1 3) + (-1 / 3 : ℂ) * (P 2 0) + (-1 / 3 : ℂ) * (P 2 1) + (1 / 3 : ℂ) * (P 2 3) + (1 / 3 : ℂ) * (P 3 0)) * g32h_omega_sq_add
  have p5 : P 1 1 = P 0 0 := by
    linear_combination ((1 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e0 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e1 + (0 + (2 / 3 : ℂ) * g32h_omega) * e4 + ((1 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e8 + (0 + (-2 / 3 : ℂ) * g32h_omega) * e16 + ((-2 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e17 + (1 / 3 : ℂ) * e19 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e20 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * g32h_omega) * e33 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e35 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * g32h_omega) * e36 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e37 + - ((7 / 9 : ℂ) * (P 0 0) + (-2 / 9 : ℂ) * (P 0 1) + (4 / 9 : ℂ) * (P 0 2) + (-7 / 9 : ℂ) * (P 1 1) + (1 / 9 : ℂ) * (P 1 3) + (2 / 9 : ℂ) * (P 2 0) + (-1 / 9 : ℂ) * (P 2 1) + (1 / 9 : ℂ) * (P 2 3) + (2 / 9 : ℂ) * (P 3 0) + (1 / 3 : ℂ) * (P 3 1)) * g32h_omega_sq_add
  have p6 : P 1 2 = 0 := by
    linear_combination ((-1 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e0 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e1 + (1 + (1 / 3 : ℂ) * g32h_omega) * e4 + ((2 / 3 : ℂ) + (2 / 3 : ℂ) * g32h_omega) * e8 + (0 + (-1 / 3 : ℂ) * g32h_omega) * e16 + ((-1 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e17 + (2 / 3 : ℂ) * e19 + ((4 / 3 : ℂ) + (2 / 3 : ℂ) * g32h_omega) * e20 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e36 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e37 + - ((-1 / 9 : ℂ) * (P 0 0) + (2 / 9 : ℂ) * (P 0 1) + (2 / 9 : ℂ) * (P 0 2) + (1 / 3 : ℂ) * (P 1 0) + (1 / 9 : ℂ) * (P 1 1) + (-1 / 3 : ℂ) * (P 1 2) + (2 / 9 : ℂ) * (P 1 3) + (4 / 9 : ℂ) * (P 2 0) + (-2 / 9 : ℂ) * (P 2 1) + (2 / 9 : ℂ) * (P 2 3) + (-2 / 9 : ℂ) * (P 3 0) + (-1 / 3 : ℂ) * (P 3 1)) * g32h_omega_sq_add
  have p7 : P 1 3 = 0 := by
    linear_combination (-1 / 3 : ℂ) * e0 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e1 + ((1 / 3 : ℂ) + (-2 / 3 : ℂ) * g32h_omega) * e4 + (-1 / 3 : ℂ) * e8 + ((-1 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e16 + (-1 / 3 : ℂ) * e17 + (0 + (1 / 3 : ℂ) * g32h_omega) * e19 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e20 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e36 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e37 + - ((1 / 9 : ℂ) * (P 0 0) + (1 / 9 : ℂ) * (P 0 1) + (1 / 9 : ℂ) * (P 0 2) + (1 / 3 : ℂ) * (P 1 0) + (-1 / 9 : ℂ) * (P 1 1) + (-5 / 9 : ℂ) * (P 1 3) + (5 / 9 : ℂ) * (P 2 0) + (2 / 9 : ℂ) * (P 2 1) + (-2 / 9 : ℂ) * (P 2 3) + (-1 / 9 : ℂ) * (P 3 0) + (1 / 3 : ℂ) * (P 3 1)) * g32h_omega_sq_add
  have p8 : P 2 0 = 0 := by
    linear_combination -1 * e4 + -1 * e8 + (1 + 1 * g32h_omega) * e16 + (0 + -1 * g32h_omega) * e17 + (0 + 1 * g32h_omega) * e19 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e33 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * g32h_omega) * e35 + 1 * e36 + - ((-2 / 3 : ℂ) * (P 0 0) + (-1 / 3 : ℂ) * (P 0 2) + (-2 / 3 : ℂ) * (P 1 0) + (2 / 3 : ℂ) * (P 1 1) + (-2 / 3 : ℂ) * (P 1 3) + (-2 / 3 : ℂ) * (P 2 0) + (2 / 3 : ℂ) * (P 2 1) + (-2 / 3 : ℂ) * (P 2 3)) * g32h_omega_sq_add
  have p9 : P 2 1 = 0 := by
    linear_combination (1 / 3 : ℂ) * e0 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e1 + ((-1 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e4 + (-2 / 3 : ℂ) * e8 + ((-2 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e16 + ((4 / 3 : ℂ) + 1 * g32h_omega) * e17 + (0 + (2 / 3 : ℂ) * g32h_omega) * e19 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e20 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e33 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e35 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * g32h_omega) * e36 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e37 + - ((2 / 9 : ℂ) * (P 0 0) + (-1 / 9 : ℂ) * (P 0 1) + (-4 / 9 : ℂ) * (P 0 2) + (-2 / 9 : ℂ) * (P 1 1) + (-4 / 9 : ℂ) * (P 1 3) + (1 / 9 : ℂ) * (P 2 0) + (-8 / 9 : ℂ) * (P 2 1) + (-4 / 9 : ℂ) * (P 2 3) + (1 / 9 : ℂ) * (P 3 0) + (-1 / 3 : ℂ) * (P 3 1)) * g32h_omega_sq_add
  have p10 : P 2 2 = P 0 0 := by
    linear_combination (0 + (-1 / 3 : ℂ) * g32h_omega) * e0 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e1 + (-1 / 3 : ℂ) * e4 + (0 + (-1 / 3 : ℂ) * g32h_omega) * e8 + ((1 / 3 : ℂ) + 1 * g32h_omega) * e16 + (0 + (2 / 3 : ℂ) * g32h_omega) * e17 + (1 + 2 * g32h_omega) * e18 + ((-1 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e19 + ((-4 / 3 : ℂ) + (-2 / 3 : ℂ) * g32h_omega) * e20 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e33 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e35 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e36 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e37 + - ((16 / 9 : ℂ) * (P 0 0) + (-8 / 9 : ℂ) * (P 0 1) + (-5 / 9 : ℂ) * (P 0 2) + (-1 / 3 : ℂ) * (P 1 0) + (-4 / 9 : ℂ) * (P 1 1) + -1 * (P 1 2) + (1 / 9 : ℂ) * (P 1 3) + (-7 / 9 : ℂ) * (P 2 0) + (-1 / 9 : ℂ) * (P 2 1) + (-4 / 3 : ℂ) * (P 2 2) + (1 / 9 : ℂ) * (P 2 3) + (-1 / 9 : ℂ) * (P 3 0) + (1 / 3 : ℂ) * (P 3 1)) * g32h_omega_sq_add
  have p11 : P 2 3 = 0 := by
    linear_combination (1 / 3 : ℂ) * e0 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e1 + ((-1 / 3 : ℂ) + (2 / 3 : ℂ) * g32h_omega) * e4 + (1 / 3 : ℂ) * e8 + ((1 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e16 + (1 / 3 : ℂ) * e17 + (1 + (5 / 3 : ℂ) * g32h_omega) * e19 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e20 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * g32h_omega) * e33 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * g32h_omega) * e35 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e36 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e37 + - ((-1 / 9 : ℂ) * (P 0 0) + (-1 / 9 : ℂ) * (P 0 1) + (-1 / 9 : ℂ) * (P 0 2) + (-1 / 3 : ℂ) * (P 1 0) + (1 / 9 : ℂ) * (P 1 1) + (-7 / 9 : ℂ) * (P 1 3) + (-5 / 9 : ℂ) * (P 2 0) + (-2 / 9 : ℂ) * (P 2 1) + (-10 / 9 : ℂ) * (P 2 3) + (1 / 9 : ℂ) * (P 3 0) + (-1 / 3 : ℂ) * (P 3 1)) * g32h_omega_sq_add
  have p12 : P 3 0 = 0 := by
    linear_combination ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * g32h_omega) * e0 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * g32h_omega) * e4 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * g32h_omega) * e8 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e16 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e17 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e19 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e33 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e35 + -1 * e36 + - ((1 / 3 : ℂ) * (P 0 1) + (2 / 3 : ℂ) * (P 1 0) + (-2 / 3 : ℂ) * (P 3 0)) * g32h_omega_sq_add
  have p13 : P 3 1 = 0 := by
    linear_combination ((1 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e0 + ((-1 / 3 : ℂ) + (-5 / 3 : ℂ) * g32h_omega) * e1 + (0 + (2 / 3 : ℂ) * g32h_omega) * e4 + ((1 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e8 + (0 + (-2 / 3 : ℂ) * g32h_omega) * e16 + ((-2 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e17 + (1 / 3 : ℂ) * e19 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e20 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e33 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * g32h_omega) * e35 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * g32h_omega) * e36 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e37 + - ((-5 / 9 : ℂ) * (P 0 0) + (-2 / 9 : ℂ) * (P 0 1) + (4 / 9 : ℂ) * (P 0 2) + 1 * (P 0 3) + (5 / 9 : ℂ) * (P 1 1) + (1 / 9 : ℂ) * (P 1 3) + (2 / 9 : ℂ) * (P 2 0) + (-1 / 9 : ℂ) * (P 2 1) + (1 / 9 : ℂ) * (P 2 3) + (2 / 9 : ℂ) * (P 3 0) + -1 * (P 3 1)) * g32h_omega_sq_add
  have p14 : P 3 2 = 0 := by
    linear_combination (0 + (-2 / 3 : ℂ) * g32h_omega) * e0 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e1 + (-1 + -2 * g32h_omega) * e2 + ((4 / 3 : ℂ) + 1 * g32h_omega) * e4 + (1 + (4 / 3 : ℂ) * g32h_omega) * e8 + (-1 / 3 : ℂ) * e16 + (-1 + (-2 / 3 : ℂ) * g32h_omega) * e17 + ((4 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e19 + ((4 / 3 : ℂ) + (2 / 3 : ℂ) * g32h_omega) * e20 + 1 * e33 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e36 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e37 + - ((-1 / 9 : ℂ) * (P 0 0) + (2 / 9 : ℂ) * (P 0 1) + (8 / 9 : ℂ) * (P 0 2) + (1 / 3 : ℂ) * (P 1 0) + (1 / 9 : ℂ) * (P 1 1) + 1 * (P 1 2) + (2 / 9 : ℂ) * (P 1 3) + (4 / 9 : ℂ) * (P 2 0) + (-2 / 9 : ℂ) * (P 2 1) + (2 / 9 : ℂ) * (P 2 3) + (-2 / 9 : ℂ) * (P 3 0) + (-1 / 3 : ℂ) * (P 3 1) + (-4 / 3 : ℂ) * (P 3 2)) * g32h_omega_sq_add
  have p15 : P 3 3 = P 0 0 := by
    linear_combination (-1 + (-1 / 3 : ℂ) * g32h_omega) * e0 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e1 + (-1 + -2 * g32h_omega) * e3 + ((2 / 3 : ℂ) + -1 * g32h_omega) * e4 + (0 + (-1 / 3 : ℂ) * g32h_omega) * e8 + (1 / 3 : ℂ) * e16 + (0 + (2 / 3 : ℂ) * g32h_omega) * e17 + ((-1 / 3 : ℂ) + (-1 / 3 : ℂ) * g32h_omega) * e19 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e20 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e33 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * g32h_omega) * e35 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e36 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * g32h_omega) * e37 + - ((16 / 9 : ℂ) * (P 0 0) + (4 / 9 : ℂ) * (P 0 1) + (1 / 9 : ℂ) * (P 0 2) + (1 / 3 : ℂ) * (P 1 0) + (-4 / 9 : ℂ) * (P 1 1) + (10 / 9 : ℂ) * (P 1 3) + (2 / 9 : ℂ) * (P 2 0) + (-1 / 9 : ℂ) * (P 2 1) + (1 / 9 : ℂ) * (P 2 3) + (-4 / 9 : ℂ) * (P 3 0) + (1 / 3 : ℂ) * (P 3 1) + (-4 / 3 : ℂ) * (P 3 3)) * g32h_omega_sq_add
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_one,
      mul_zero, Fin.isValue, reduceCtorEq, if_true, if_false,
      p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]

end HodgeLean.Foundations.Program
