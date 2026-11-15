import HodgeLean.Foundations.Program.G32PropFourSixDefs

noncomputable section

open HodgeLean.Papers

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
theorem g32p_matrix_commutant {K : Type*} [Field K] [CharZero K]
    (w : K) (hw : w ^ 2 + w + 1 = 0) (M : Matrix (Fin 4) (Fin 4) K)
    (h1 : M * g32R1 w = g32R1 w * M)
    (h2 : M * g32R2 w = g32R2 w * M)
    (hx : M * g32X w = g32X w * M) : M = M 3 3 • (1 : Matrix (Fin 4) (Fin 4) K) := by
  have e0 := congrFun (congrFun h1 0) 0
  norm_num [Matrix.mul_apply, Fin.sum_univ_four, g32R1] at e0
  have e1 := congrFun (congrFun h1 0) 1
  norm_num [Matrix.mul_apply, Fin.sum_univ_four, g32R1] at e1
  have e2 := congrFun (congrFun h1 0) 2
  norm_num [Matrix.mul_apply, Fin.sum_univ_four, g32R1] at e2
  have e3 := congrFun (congrFun h1 0) 3
  norm_num [Matrix.mul_apply, Fin.sum_univ_four, g32R1] at e3
  have e4 := congrFun (congrFun h1 1) 0
  norm_num [Matrix.mul_apply, Fin.sum_univ_four, g32R1] at e4
  have e8 := congrFun (congrFun h1 2) 0
  norm_num [Matrix.mul_apply, Fin.sum_univ_four, g32R1] at e8
  have e16 := congrFun (congrFun h2 0) 0
  norm_num [Matrix.mul_apply, Fin.sum_univ_four, g32R2] at e16
  have e17 := congrFun (congrFun h2 0) 1
  norm_num [Matrix.mul_apply, Fin.sum_univ_four, g32R2] at e17
  have e18 := congrFun (congrFun h2 0) 2
  norm_num [Matrix.mul_apply, Fin.sum_univ_four, g32R2] at e18
  have e19 := congrFun (congrFun h2 0) 3
  norm_num [Matrix.mul_apply, Fin.sum_univ_four, g32R2] at e19
  have e20 := congrFun (congrFun h2 1) 0
  norm_num [Matrix.mul_apply, Fin.sum_univ_four, g32R2] at e20
  have e33 := congrFun (congrFun hx 0) 1
  norm_num [Matrix.mul_apply, Fin.sum_univ_four, g32X] at e33
  have e35 := congrFun (congrFun hx 0) 3
  norm_num [Matrix.mul_apply, Fin.sum_univ_four, g32X] at e35
  have e36 := congrFun (congrFun hx 1) 0
  norm_num [Matrix.mul_apply, Fin.sum_univ_four, g32X] at e36
  have e37 := congrFun (congrFun hx 1) 1
  norm_num [Matrix.mul_apply, Fin.sum_univ_four, g32X] at e37
  have m00 : M 0 0 = M 3 3 := by
    linear_combination ((1 / 3 : K) * w + (1 : K)) * e0 + ((-1 / 3 : K) * w + (-2 / 3 : K)) * e1 + ((2 : K) * w + (1 : K)) * e3 + ((1 : K) * w + (-2 / 3 : K)) * e4 + ((1 / 3 : K) * w) * e8 + ((-1 / 3 : K)) * e16 + ((-2 / 3 : K) * w) * e17 + ((1 / 3 : K) * w + (1 / 3 : K)) * e19 + ((-1 / 3 : K) * w + (-2 / 3 : K)) * e20 + ((-1 / 3 : K) * w + (1 / 3 : K)) * e33 + ((-2 / 3 : K) * w + (-1 / 3 : K)) * e35 + ((-1 / 3 : K) * w + (1 / 3 : K)) * e36 + ((-1 / 3 : K) * w + (1 / 3 : K)) * e37 - (((-16 / 9 : K)) * M 0 0 + ((-4 / 9 : K)) * M 0 1 + ((-1 / 9 : K)) * M 0 2 + ((-1 / 3 : K)) * M 1 0 + ((4 / 9 : K)) * M 1 1 + ((-10 / 9 : K)) * M 1 3 + ((-2 / 9 : K)) * M 2 0 + ((1 / 9 : K)) * M 2 1 + ((-1 / 9 : K)) * M 2 3 + ((4 / 9 : K)) * M 3 0 + ((-1 / 3 : K)) * M 3 1 + ((4 / 3 : K)) * M 3 3) * hw
  have m01 : M 0 1 = 0 := by
    linear_combination ((1 / 3 : K) * w + (-1 / 3 : K)) * e0 + ((-2 / 3 : K) * w + (-1 / 3 : K)) * e4 + ((-2 / 3 : K) * w + (-1 / 3 : K)) * e8 + ((-1 / 3 : K) * w + (1 / 3 : K)) * e16 + ((1 / 3 : K) * w + (2 / 3 : K)) * e17 + ((-1 / 3 : K) * w + (-2 / 3 : K)) * e19 + ((2 / 3 : K) * w + (1 / 3 : K)) * e33 + ((1 / 3 : K) * w + (2 / 3 : K)) * e35 - (((-1 / 3 : K)) * M 0 1 + ((1 / 3 : K)) * M 0 2) * hw
  have m02 : M 0 2 = 0 := by
    linear_combination ((-2 / 3 : K) * w + (-1 / 3 : K)) * e0 + ((1 / 3 : K) * w + (2 / 3 : K)) * e4 + ((1 / 3 : K) * w + (2 / 3 : K)) * e8 + ((2 / 3 : K) * w + (1 / 3 : K)) * e16 + ((1 / 3 : K) * w + (-1 / 3 : K)) * e17 + ((-1 / 3 : K) * w + (1 / 3 : K)) * e19 + ((-1 : K) * w) * e33 - (((1 / 3 : K)) * M 0 0 + ((1 / 3 : K)) * M 0 1 + ((-2 / 3 : K)) * M 0 2 + ((-1 / 3 : K)) * M 1 1 + ((1 / 3 : K)) * M 1 3 + ((-1 / 3 : K)) * M 2 0 + ((-1 / 3 : K)) * M 2 1 + ((1 / 3 : K)) * M 2 3 + ((-1 / 3 : K)) * M 3 0) * hw
  have m03 : M 0 3 = 0 := by
    linear_combination ((1 / 3 : K) * w + (-1 / 3 : K)) * e33 + ((-1 / 3 : K) * w + (1 / 3 : K)) * e35 - (((-1 / 3 : K)) * M 0 3) * hw
  have m10 : M 1 0 = 0 := by
    linear_combination ((2 / 3 : K) * w + (1 / 3 : K)) * e0 + ((-1 / 3 : K) * w + (1 / 3 : K)) * e4 + ((-1 / 3 : K) * w + (1 / 3 : K)) * e8 + ((1 / 3 : K) * w + (-1 / 3 : K)) * e16 + ((2 / 3 : K) * w + (1 / 3 : K)) * e17 + ((-2 / 3 : K) * w + (-1 / 3 : K)) * e19 + ((-1 : K)) * e36 - (((1 / 3 : K)) * M 0 0 + ((-1 / 3 : K)) * M 0 1 + ((-1 / 3 : K)) * M 0 2 + ((-2 / 3 : K)) * M 1 0 + ((-1 / 3 : K)) * M 1 1 + ((1 / 3 : K)) * M 1 3 + ((-1 / 3 : K)) * M 2 0 + ((-1 / 3 : K)) * M 2 1 + ((1 / 3 : K)) * M 2 3 + ((1 / 3 : K)) * M 3 0) * hw
  have m11 : M 1 1 = M 3 3 := by
    linear_combination ((2 / 3 : K) * w + (4 / 3 : K)) * e0 + ((2 : K) * w + (1 : K)) * e3 + ((5 / 3 : K) * w + (-2 / 3 : K)) * e4 + ((2 / 3 : K) * w + (1 / 3 : K)) * e8 + ((-2 / 3 : K) * w + (-1 / 3 : K)) * e16 + ((-1 / 3 : K) * w + (-2 / 3 : K)) * e17 + ((1 / 3 : K) * w + (2 / 3 : K)) * e19 + ((1 / 3 : K) * w + (2 / 3 : K)) * e33 + ((-1 / 3 : K) * w + (-2 / 3 : K)) * e35 + ((-1 : K) * w) * e36 - (((-1 : K)) * M 0 0 + ((-2 / 3 : K)) * M 0 1 + ((1 / 3 : K)) * M 0 2 + ((-1 / 3 : K)) * M 1 0 + ((-1 / 3 : K)) * M 1 1 + ((-1 : K)) * M 1 3 + ((2 / 3 : K)) * M 3 0 + ((4 / 3 : K)) * M 3 3) * hw
  have m12 : M 1 2 = 0 := by
    linear_combination ((-1 / 3 : K) * w + (-1 / 3 : K)) * e0 + ((-1 / 3 : K) * w + (-2 / 3 : K)) * e1 + ((1 / 3 : K) * w + (1 : K)) * e4 + ((2 / 3 : K) * w + (2 / 3 : K)) * e8 + ((-1 / 3 : K) * w) * e16 + ((-1 / 3 : K) * w + (-1 / 3 : K)) * e17 + ((2 / 3 : K)) * e19 + ((2 / 3 : K) * w + (4 / 3 : K)) * e20 + ((-1 / 3 : K) * w + (-2 / 3 : K)) * e36 + ((-1 / 3 : K) * w + (1 / 3 : K)) * e37 - (((-1 / 9 : K)) * M 0 0 + ((2 / 9 : K)) * M 0 1 + ((2 / 9 : K)) * M 0 2 + ((1 / 3 : K)) * M 1 0 + ((1 / 9 : K)) * M 1 1 + ((-1 / 3 : K)) * M 1 2 + ((2 / 9 : K)) * M 1 3 + ((4 / 9 : K)) * M 2 0 + ((-2 / 9 : K)) * M 2 1 + ((2 / 9 : K)) * M 2 3 + ((-2 / 9 : K)) * M 3 0 + ((-1 / 3 : K)) * M 3 1) * hw
  have m13 : M 1 3 = 0 := by
    linear_combination ((-1 / 3 : K)) * e0 + ((1 / 3 : K) * w + (2 / 3 : K)) * e1 + ((-2 / 3 : K) * w + (1 / 3 : K)) * e4 + ((-1 / 3 : K)) * e8 + ((-1 / 3 : K) * w + (-1 / 3 : K)) * e16 + ((-1 / 3 : K)) * e17 + ((1 / 3 : K) * w) * e19 + ((1 / 3 : K) * w + (2 / 3 : K)) * e20 + ((1 / 3 : K) * w + (-1 / 3 : K)) * e36 + ((1 / 3 : K) * w + (-1 / 3 : K)) * e37 - (((1 / 9 : K)) * M 0 0 + ((1 / 9 : K)) * M 0 1 + ((1 / 9 : K)) * M 0 2 + ((1 / 3 : K)) * M 1 0 + ((-1 / 9 : K)) * M 1 1 + ((-5 / 9 : K)) * M 1 3 + ((5 / 9 : K)) * M 2 0 + ((2 / 9 : K)) * M 2 1 + ((-2 / 9 : K)) * M 2 3 + ((-1 / 9 : K)) * M 3 0 + ((1 / 3 : K)) * M 3 1) * hw
  have m20 : M 2 0 = 0 := by
    linear_combination ((-1 : K)) * e4 + ((-1 : K)) * e8 + ((1 : K) * w + (1 : K)) * e16 + ((-1 : K) * w) * e17 + ((1 : K) * w) * e19 + ((-1 / 3 : K) * w + (-2 / 3 : K)) * e33 + ((-2 / 3 : K) * w + (-1 / 3 : K)) * e35 + ((1 : K)) * e36 - (((-2 / 3 : K)) * M 0 0 + ((-1 / 3 : K)) * M 0 2 + ((-2 / 3 : K)) * M 1 0 + ((2 / 3 : K)) * M 1 1 + ((-2 / 3 : K)) * M 1 3 + ((-2 / 3 : K)) * M 2 0 + ((2 / 3 : K)) * M 2 1 + ((-2 / 3 : K)) * M 2 3) * hw
  have m21 : M 2 1 = 0 := by
    linear_combination ((1 / 3 : K)) * e0 + ((-1 / 3 : K) * w + (-2 / 3 : K)) * e1 + ((-1 / 3 : K) * w + (-1 / 3 : K)) * e4 + ((-2 / 3 : K)) * e8 + ((1 / 3 : K) * w + (-2 / 3 : K)) * e16 + ((1 : K) * w + (4 / 3 : K)) * e17 + ((2 / 3 : K) * w) * e19 + ((-1 / 3 : K) * w + (-2 / 3 : K)) * e20 + ((1 / 3 : K) * w + (2 / 3 : K)) * e33 + ((-1 / 3 : K) * w + (1 / 3 : K)) * e35 + ((2 / 3 : K) * w + (1 / 3 : K)) * e36 + ((-1 / 3 : K) * w + (1 / 3 : K)) * e37 - (((2 / 9 : K)) * M 0 0 + ((-1 / 9 : K)) * M 0 1 + ((-4 / 9 : K)) * M 0 2 + ((-2 / 9 : K)) * M 1 1 + ((-4 / 9 : K)) * M 1 3 + ((1 / 9 : K)) * M 2 0 + ((-8 / 9 : K)) * M 2 1 + ((-4 / 9 : K)) * M 2 3 + ((1 / 9 : K)) * M 3 0 + ((-1 / 3 : K)) * M 3 1) * hw
  have m22 : M 2 2 = M 3 3 := by
    linear_combination ((1 : K)) * e0 + ((2 : K) * w + (1 : K)) * e3 + ((1 : K) * w + (-1 : K)) * e4 + ((1 : K) * w) * e16 + ((2 : K) * w + (1 : K)) * e18 + ((-1 : K) * w + (-2 : K)) * e20 + ((-2 / 3 : K) * w + (-1 / 3 : K)) * e33 + ((-1 / 3 : K) * w + (-2 / 3 : K)) * e35 + ((1 : K)) * e36 - (((-4 / 3 : K)) * M 0 1 + ((-2 / 3 : K)) * M 0 2 + ((-2 / 3 : K)) * M 1 0 + ((-1 : K)) * M 1 2 + ((-1 : K)) * M 1 3 + ((-1 : K)) * M 2 0 + ((-4 / 3 : K)) * M 2 2 + ((1 / 3 : K)) * M 3 0 + ((4 / 3 : K)) * M 3 3) * hw
  have m23 : M 2 3 = 0 := by
    linear_combination ((1 / 3 : K)) * e0 + ((-1 / 3 : K) * w + (-2 / 3 : K)) * e1 + ((2 / 3 : K) * w + (-1 / 3 : K)) * e4 + ((1 / 3 : K)) * e8 + ((1 / 3 : K) * w + (1 / 3 : K)) * e16 + ((1 / 3 : K)) * e17 + ((5 / 3 : K) * w + (1 : K)) * e19 + ((-1 / 3 : K) * w + (-2 / 3 : K)) * e20 + ((2 / 3 : K) * w + (1 / 3 : K)) * e33 + ((-2 / 3 : K) * w + (-1 / 3 : K)) * e35 + ((-1 / 3 : K) * w + (1 / 3 : K)) * e36 + ((-1 / 3 : K) * w + (1 / 3 : K)) * e37 - (((-1 / 9 : K)) * M 0 0 + ((-1 / 9 : K)) * M 0 1 + ((-1 / 9 : K)) * M 0 2 + ((-1 / 3 : K)) * M 1 0 + ((1 / 9 : K)) * M 1 1 + ((-7 / 9 : K)) * M 1 3 + ((-5 / 9 : K)) * M 2 0 + ((-2 / 9 : K)) * M 2 1 + ((-10 / 9 : K)) * M 2 3 + ((1 / 9 : K)) * M 3 0 + ((-1 / 3 : K)) * M 3 1) * hw
  have m30 : M 3 0 = 0 := by
    linear_combination ((-2 / 3 : K) * w + (-1 / 3 : K)) * e0 + ((-2 / 3 : K) * w + (-1 / 3 : K)) * e4 + ((-2 / 3 : K) * w + (-1 / 3 : K)) * e8 + ((-1 / 3 : K) * w + (-2 / 3 : K)) * e16 + ((1 / 3 : K) * w + (2 / 3 : K)) * e17 + ((-1 / 3 : K) * w + (-2 / 3 : K)) * e19 + ((-1 / 3 : K) * w + (1 / 3 : K)) * e33 + ((1 / 3 : K) * w + (2 / 3 : K)) * e35 + ((-1 : K)) * e36 - (((1 / 3 : K)) * M 0 1 + ((2 / 3 : K)) * M 1 0 + ((-2 / 3 : K)) * M 3 0) * hw
  have m31 : M 3 1 = 0 := by
    linear_combination ((1 / 3 : K) * w + (1 / 3 : K)) * e0 + ((-5 / 3 : K) * w + (-1 / 3 : K)) * e1 + ((2 / 3 : K) * w) * e4 + ((1 / 3 : K) * w + (1 / 3 : K)) * e8 + ((-2 / 3 : K) * w) * e16 + ((1 / 3 : K) * w + (-2 / 3 : K)) * e17 + ((1 / 3 : K)) * e19 + ((1 / 3 : K) * w + (2 / 3 : K)) * e20 + ((1 / 3 : K) * w + (-1 / 3 : K)) * e33 + ((2 / 3 : K) * w + (1 / 3 : K)) * e35 + ((-2 / 3 : K) * w + (-1 / 3 : K)) * e36 + ((1 / 3 : K) * w + (-1 / 3 : K)) * e37 - (((-5 / 9 : K)) * M 0 0 + ((-2 / 9 : K)) * M 0 1 + ((4 / 9 : K)) * M 0 2 + ((1 : K)) * M 0 3 + ((5 / 9 : K)) * M 1 1 + ((1 / 9 : K)) * M 1 3 + ((2 / 9 : K)) * M 2 0 + ((-1 / 9 : K)) * M 2 1 + ((1 / 9 : K)) * M 2 3 + ((2 / 9 : K)) * M 3 0 + ((-1 : K)) * M 3 1) * hw
  have m32 : M 3 2 = 0 := by
    linear_combination ((-2 / 3 : K) * w) * e0 + ((-1 / 3 : K) * w + (-2 / 3 : K)) * e1 + ((-2 : K) * w + (-1 : K)) * e2 + ((1 : K) * w + (4 / 3 : K)) * e4 + ((4 / 3 : K) * w + (1 : K)) * e8 + ((-1 / 3 : K)) * e16 + ((-2 / 3 : K) * w + (-1 : K)) * e17 + ((1 / 3 : K) * w + (4 / 3 : K)) * e19 + ((2 / 3 : K) * w + (4 / 3 : K)) * e20 + ((1 : K)) * e33 + ((-1 / 3 : K) * w + (-2 / 3 : K)) * e36 + ((-1 / 3 : K) * w + (1 / 3 : K)) * e37 - (((-1 / 9 : K)) * M 0 0 + ((2 / 9 : K)) * M 0 1 + ((8 / 9 : K)) * M 0 2 + ((1 / 3 : K)) * M 1 0 + ((1 / 9 : K)) * M 1 1 + ((1 : K)) * M 1 2 + ((2 / 9 : K)) * M 1 3 + ((4 / 9 : K)) * M 2 0 + ((-2 / 9 : K)) * M 2 1 + ((2 / 9 : K)) * M 2 3 + ((-2 / 9 : K)) * M 3 0 + ((-1 / 3 : K)) * M 3 1 + ((-4 / 3 : K)) * M 3 2) * hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.smul_apply, Matrix.one_apply] <;> assumption

end HodgeLean.Foundations.Program
