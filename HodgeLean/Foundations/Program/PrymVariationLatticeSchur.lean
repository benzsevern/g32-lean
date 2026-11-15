import HodgeLean.Foundations.Program.PrymVariationLatticeProjector

set_option maxHeartbeats 400000

/-! # Schur's lemma for the printed G32 generators

Two finite linear-algebra facts about the printed generators `r₁, r₂, x`: a matrix commuting
with all three is scalar, and a matrix intertwining them with their complex conjugates is zero.
Averaging over the group then gives the matrix-coefficient orthogonality used for the primitive
projector. HC no distance; AV milestone no distance.
-/

open HodgeLean.Papers
open scoped Matrix

namespace HodgeLean.Foundations.Program

/-- A matrix commuting with the printed generators `r₁, r₂, x` is scalar.
Source: Serre, *Linear Representations of Finite Groups*, §2.2 (Schur's lemma); the exact
linear relations are checked below over `ℚ(ω)`. -/
theorem b63l_schur_scalar (w : ℂ) (hw : w ^ 2 + w + 1 = 0) (Y : Matrix (Fin 4) (Fin 4) ℂ)
    (h0 : g32R1 w * Y = Y * g32R1 w) (h1 : g32R2 w * Y = Y * g32R2 w)
    (h2 : g32X w * Y = Y * g32X w) :
    Y = Y 0 0 • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have e000 : (w + 2) / 3 * Y 0 0 + (2 * w + 1) / 3 * Y 1 0 + 0 * Y 2 0 + -((2 * w + 1) / 3) * Y 3 0 = Y 0 0 * ((w + 2) / 3) + Y 0 1 * (-((w + 2) / 3)) + Y 0 2 * (0) + Y 0 3 * ((w + 2) / 3) := by
    have h' := congrFun (congrFun h0 0) 0
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e001 : (w + 2) / 3 * Y 0 1 + (2 * w + 1) / 3 * Y 1 1 + 0 * Y 2 1 + -((2 * w + 1) / 3) * Y 3 1 = Y 0 0 * ((2 * w + 1) / 3) + Y 0 1 * ((w + 2) / 3) + Y 0 2 * (0) + Y 0 3 * ((1 - w) / 3) := by
    have h' := congrFun (congrFun h0 0) 1
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e002 : (w + 2) / 3 * Y 0 2 + (2 * w + 1) / 3 * Y 1 2 + 0 * Y 2 2 + -((2 * w + 1) / 3) * Y 3 2 = Y 0 0 * (0) + Y 0 1 * (0) + Y 0 2 * (1) + Y 0 3 * (0) := by
    have h' := congrFun (congrFun h0 0) 2
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e003 : (w + 2) / 3 * Y 0 3 + (2 * w + 1) / 3 * Y 1 3 + 0 * Y 2 3 + -((2 * w + 1) / 3) * Y 3 3 = Y 0 0 * (-((2 * w + 1) / 3)) + Y 0 1 * ((1 - w) / 3) + Y 0 2 * (0) + Y 0 3 * ((w + 2) / 3) := by
    have h' := congrFun (congrFun h0 0) 3
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e010 : -((w + 2) / 3) * Y 0 0 + (w + 2) / 3 * Y 1 0 + 0 * Y 2 0 + (1 - w) / 3 * Y 3 0 = Y 1 0 * ((w + 2) / 3) + Y 1 1 * (-((w + 2) / 3)) + Y 1 2 * (0) + Y 1 3 * ((w + 2) / 3) := by
    have h' := congrFun (congrFun h0 1) 0
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e020 : 0 * Y 0 0 + 0 * Y 1 0 + 1 * Y 2 0 + 0 * Y 3 0 = Y 2 0 * ((w + 2) / 3) + Y 2 1 * (-((w + 2) / 3)) + Y 2 2 * (0) + Y 2 3 * ((w + 2) / 3) := by
    have h' := congrFun (congrFun h0 2) 0
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e100 : (1 - w) / 3 * Y 0 0 + (2 * w + 1) / 3 * Y 1 0 + (2 * w + 1) / 3 * Y 2 0 + 0 * Y 3 0 = Y 0 0 * ((1 - w) / 3) + Y 0 1 * ((1 - w) / 3) + Y 0 2 * ((1 - w) / 3) + Y 0 3 * (0) := by
    have h' := congrFun (congrFun h1 0) 0
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e101 : (1 - w) / 3 * Y 0 1 + (2 * w + 1) / 3 * Y 1 1 + (2 * w + 1) / 3 * Y 2 1 + 0 * Y 3 1 = Y 0 0 * ((2 * w + 1) / 3) + Y 0 1 * ((1 - w) / 3) + Y 0 2 * (-((w + 2) / 3)) + Y 0 3 * (0) := by
    have h' := congrFun (congrFun h1 0) 1
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e102 : (1 - w) / 3 * Y 0 2 + (2 * w + 1) / 3 * Y 1 2 + (2 * w + 1) / 3 * Y 2 2 + 0 * Y 3 2 = Y 0 0 * ((2 * w + 1) / 3) + Y 0 1 * (-((w + 2) / 3)) + Y 0 2 * ((1 - w) / 3) + Y 0 3 * (0) := by
    have h' := congrFun (congrFun h1 0) 2
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e103 : (1 - w) / 3 * Y 0 3 + (2 * w + 1) / 3 * Y 1 3 + (2 * w + 1) / 3 * Y 2 3 + 0 * Y 3 3 = Y 0 0 * (0) + Y 0 1 * (0) + Y 0 2 * (0) + Y 0 3 * (1) := by
    have h' := congrFun (congrFun h1 0) 3
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e110 : (1 - w) / 3 * Y 0 0 + (1 - w) / 3 * Y 1 0 + -((w + 2) / 3) * Y 2 0 + 0 * Y 3 0 = Y 1 0 * ((1 - w) / 3) + Y 1 1 * ((1 - w) / 3) + Y 1 2 * ((1 - w) / 3) + Y 1 3 * (0) := by
    have h' := congrFun (congrFun h1 1) 0
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e201 : -1 * Y 0 1 + 0 * Y 1 1 + 0 * Y 2 1 + 0 * Y 3 1 = Y 0 0 * (0) + Y 0 1 * (-((w + 2) / 3)) + Y 0 2 * ((w + 2) / 3) + Y 0 3 * (-((w + 2) / 3)) := by
    have h' := congrFun (congrFun h2 0) 1
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e203 : -1 * Y 0 3 + 0 * Y 1 3 + 0 * Y 2 3 + 0 * Y 3 3 = Y 0 0 * (0) + Y 0 1 * ((1 - w) / 3) + Y 0 2 * ((w + 2) / 3) + Y 0 3 * ((2 * w + 1) / 3) := by
    have h' := congrFun (congrFun h2 0) 3
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e210 : 0 * Y 0 0 + -((w + 2) / 3) * Y 1 0 + -((2 * w + 1) / 3) * Y 2 0 + (1 - w) / 3 * Y 3 0 = Y 1 0 * (-1) + Y 1 1 * (0) + Y 1 2 * (0) + Y 1 3 * (0) := by
    have h' := congrFun (congrFun h2 1) 0
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e211 : 0 * Y 0 1 + -((w + 2) / 3) * Y 1 1 + -((2 * w + 1) / 3) * Y 2 1 + (1 - w) / 3 * Y 3 1 = Y 1 0 * (0) + Y 1 1 * (-((w + 2) / 3)) + Y 1 2 * ((w + 2) / 3) + Y 1 3 * (-((w + 2) / 3)) := by
    have h' := congrFun (congrFun h2 1) 1
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have z01 : Y 0 1 = 0 := by
    linear_combination ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e000 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e010 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e020 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e100 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e101 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e103 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e201 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e203 + ((1 / 3 : ℂ) * Y 0 1 + (-1 / 3 : ℂ) * Y 0 2) * hw
  have z02 : Y 0 2 = 0 := by
    linear_combination ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e000 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e010 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e020 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e100 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e101 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e103 + ((0 : ℂ) + (1 : ℂ) * w) * e201 + ((-1 / 3 : ℂ) * Y 0 0 + (-1 / 3 : ℂ) * Y 0 1 + (2 / 3 : ℂ) * Y 0 2 + (1 / 3 : ℂ) * Y 1 1 + (-1 / 3 : ℂ) * Y 1 3 + (1 / 3 : ℂ) * Y 2 0 + (1 / 3 : ℂ) * Y 2 1 + (-1 / 3 : ℂ) * Y 2 3 + (1 / 3 : ℂ) * Y 3 0) * hw
  have z03 : Y 0 3 = 0 := by
    linear_combination ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e201 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e203 + ((1 / 3 : ℂ) * Y 0 3) * hw
  have z10 : Y 1 0 = 0 := by
    linear_combination ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e000 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e010 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e020 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e100 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e101 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e103 + ((1 : ℂ) + (0 : ℂ) * w) * e210 + ((-1 / 3 : ℂ) * Y 0 0 + (1 / 3 : ℂ) * Y 0 1 + (1 / 3 : ℂ) * Y 0 2 + (2 / 3 : ℂ) * Y 1 0 + (1 / 3 : ℂ) * Y 1 1 + (-1 / 3 : ℂ) * Y 1 3 + (1 / 3 : ℂ) * Y 2 0 + (1 / 3 : ℂ) * Y 2 1 + (-1 / 3 : ℂ) * Y 2 3 + (-1 / 3 : ℂ) * Y 3 0) * hw
  have z11 : Y 1 1 = Y 0 0 := by
    linear_combination ((-1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e000 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e001 + ((0 : ℂ) + (-2 / 3 : ℂ) * w) * e010 + ((-1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e020 + ((0 : ℂ) + (2 / 3 : ℂ) * w) * e100 + ((2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e101 + ((-1 / 3 : ℂ) + (0 : ℂ) * w) * e103 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e110 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e201 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e203 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e210 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e211 + ((-7 / 9 : ℂ) * Y 0 0 + (2 / 9 : ℂ) * Y 0 1 + (-4 / 9 : ℂ) * Y 0 2 + (7 / 9 : ℂ) * Y 1 1 + (-1 / 9 : ℂ) * Y 1 3 + (-2 / 9 : ℂ) * Y 2 0 + (1 / 9 : ℂ) * Y 2 1 + (-1 / 9 : ℂ) * Y 2 3 + (-2 / 9 : ℂ) * Y 3 0 + (-1 / 3 : ℂ) * Y 3 1) * hw
  have z12 : Y 1 2 = 0 := by
    linear_combination ((1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e000 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e001 + ((-1 : ℂ) + (-1 / 3 : ℂ) * w) * e010 + ((-2 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e020 + ((0 : ℂ) + (1 / 3 : ℂ) * w) * e100 + ((1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e101 + ((-2 / 3 : ℂ) + (0 : ℂ) * w) * e103 + ((-4 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e110 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e210 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e211 + ((1 / 9 : ℂ) * Y 0 0 + (-2 / 9 : ℂ) * Y 0 1 + (-2 / 9 : ℂ) * Y 0 2 + (-1 / 3 : ℂ) * Y 1 0 + (-1 / 9 : ℂ) * Y 1 1 + (1 / 3 : ℂ) * Y 1 2 + (-2 / 9 : ℂ) * Y 1 3 + (-4 / 9 : ℂ) * Y 2 0 + (2 / 9 : ℂ) * Y 2 1 + (-2 / 9 : ℂ) * Y 2 3 + (2 / 9 : ℂ) * Y 3 0 + (1 / 3 : ℂ) * Y 3 1) * hw
  have z13 : Y 1 3 = 0 := by
    linear_combination ((1 / 3 : ℂ) + (0 : ℂ) * w) * e000 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e001 + ((-1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e010 + ((1 / 3 : ℂ) + (0 : ℂ) * w) * e020 + ((1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e100 + ((1 / 3 : ℂ) + (0 : ℂ) * w) * e101 + ((0 : ℂ) + (-1 / 3 : ℂ) * w) * e103 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e110 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e210 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e211 + ((-1 / 9 : ℂ) * Y 0 0 + (-1 / 9 : ℂ) * Y 0 1 + (-1 / 9 : ℂ) * Y 0 2 + (-1 / 3 : ℂ) * Y 1 0 + (1 / 9 : ℂ) * Y 1 1 + (5 / 9 : ℂ) * Y 1 3 + (-5 / 9 : ℂ) * Y 2 0 + (-2 / 9 : ℂ) * Y 2 1 + (2 / 9 : ℂ) * Y 2 3 + (1 / 9 : ℂ) * Y 3 0 + (-1 / 3 : ℂ) * Y 3 1) * hw
  have z20 : Y 2 0 = 0 := by
    linear_combination ((1 : ℂ) + (0 : ℂ) * w) * e010 + ((1 : ℂ) + (0 : ℂ) * w) * e020 + ((-1 : ℂ) + (-1 : ℂ) * w) * e100 + ((0 : ℂ) + (1 : ℂ) * w) * e101 + ((0 : ℂ) + (-1 : ℂ) * w) * e103 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e201 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e203 + ((-1 : ℂ) + (0 : ℂ) * w) * e210 + ((2 / 3 : ℂ) * Y 0 0 + (1 / 3 : ℂ) * Y 0 2 + (2 / 3 : ℂ) * Y 1 0 + (-2 / 3 : ℂ) * Y 1 1 + (2 / 3 : ℂ) * Y 1 3 + (2 / 3 : ℂ) * Y 2 0 + (-2 / 3 : ℂ) * Y 2 1 + (2 / 3 : ℂ) * Y 2 3) * hw
  have z21 : Y 2 1 = 0 := by
    linear_combination ((-1 / 3 : ℂ) + (0 : ℂ) * w) * e000 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e001 + ((1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e010 + ((2 / 3 : ℂ) + (0 : ℂ) * w) * e020 + ((2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e100 + ((-4 / 3 : ℂ) + (-1 : ℂ) * w) * e101 + ((0 : ℂ) + (-2 / 3 : ℂ) * w) * e103 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e110 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e201 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e203 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e210 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e211 + ((-2 / 9 : ℂ) * Y 0 0 + (1 / 9 : ℂ) * Y 0 1 + (4 / 9 : ℂ) * Y 0 2 + (2 / 9 : ℂ) * Y 1 1 + (4 / 9 : ℂ) * Y 1 3 + (-1 / 9 : ℂ) * Y 2 0 + (8 / 9 : ℂ) * Y 2 1 + (4 / 9 : ℂ) * Y 2 3 + (-1 / 9 : ℂ) * Y 3 0 + (1 / 3 : ℂ) * Y 3 1) * hw
  have z22 : Y 2 2 = Y 0 0 := by
    linear_combination ((0 : ℂ) + (1 / 3 : ℂ) * w) * e000 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e001 + ((1 / 3 : ℂ) + (0 : ℂ) * w) * e010 + ((0 : ℂ) + (1 / 3 : ℂ) * w) * e020 + ((-1 / 3 : ℂ) + (-1 : ℂ) * w) * e100 + ((0 : ℂ) + (-2 / 3 : ℂ) * w) * e101 + ((-1 : ℂ) + (-2 : ℂ) * w) * e102 + ((1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e103 + ((4 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e110 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e201 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e203 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e210 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e211 + ((-16 / 9 : ℂ) * Y 0 0 + (8 / 9 : ℂ) * Y 0 1 + (5 / 9 : ℂ) * Y 0 2 + (1 / 3 : ℂ) * Y 1 0 + (4 / 9 : ℂ) * Y 1 1 + (1 : ℂ) * Y 1 2 + (-1 / 9 : ℂ) * Y 1 3 + (7 / 9 : ℂ) * Y 2 0 + (1 / 9 : ℂ) * Y 2 1 + (4 / 3 : ℂ) * Y 2 2 + (-1 / 9 : ℂ) * Y 2 3 + (1 / 9 : ℂ) * Y 3 0 + (-1 / 3 : ℂ) * Y 3 1) * hw
  have z23 : Y 2 3 = 0 := by
    linear_combination ((-1 / 3 : ℂ) + (0 : ℂ) * w) * e000 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e001 + ((1 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e010 + ((-1 / 3 : ℂ) + (0 : ℂ) * w) * e020 + ((-1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e100 + ((-1 / 3 : ℂ) + (0 : ℂ) * w) * e101 + ((-1 : ℂ) + (-5 / 3 : ℂ) * w) * e103 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e110 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e201 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e203 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e210 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e211 + ((1 / 9 : ℂ) * Y 0 0 + (1 / 9 : ℂ) * Y 0 1 + (1 / 9 : ℂ) * Y 0 2 + (1 / 3 : ℂ) * Y 1 0 + (-1 / 9 : ℂ) * Y 1 1 + (7 / 9 : ℂ) * Y 1 3 + (5 / 9 : ℂ) * Y 2 0 + (2 / 9 : ℂ) * Y 2 1 + (10 / 9 : ℂ) * Y 2 3 + (-1 / 9 : ℂ) * Y 3 0 + (1 / 3 : ℂ) * Y 3 1) * hw
  have z30 : Y 3 0 = 0 := by
    linear_combination ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e000 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e010 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e020 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e100 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e101 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e103 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e201 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e203 + ((1 : ℂ) + (0 : ℂ) * w) * e210 + ((-1 / 3 : ℂ) * Y 0 1 + (-2 / 3 : ℂ) * Y 1 0 + (2 / 3 : ℂ) * Y 3 0) * hw
  have z31 : Y 3 1 = 0 := by
    linear_combination ((-1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e000 + ((1 / 3 : ℂ) + (5 / 3 : ℂ) * w) * e001 + ((0 : ℂ) + (-2 / 3 : ℂ) * w) * e010 + ((-1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e020 + ((0 : ℂ) + (2 / 3 : ℂ) * w) * e100 + ((2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e101 + ((-1 / 3 : ℂ) + (0 : ℂ) * w) * e103 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e110 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e201 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e203 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e210 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e211 + ((5 / 9 : ℂ) * Y 0 0 + (2 / 9 : ℂ) * Y 0 1 + (-4 / 9 : ℂ) * Y 0 2 + (-1 : ℂ) * Y 0 3 + (-5 / 9 : ℂ) * Y 1 1 + (-1 / 9 : ℂ) * Y 1 3 + (-2 / 9 : ℂ) * Y 2 0 + (1 / 9 : ℂ) * Y 2 1 + (-1 / 9 : ℂ) * Y 2 3 + (-2 / 9 : ℂ) * Y 3 0 + (1 : ℂ) * Y 3 1) * hw
  have z32 : Y 3 2 = 0 := by
    linear_combination ((0 : ℂ) + (2 / 3 : ℂ) * w) * e000 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e001 + ((1 : ℂ) + (2 : ℂ) * w) * e002 + ((-4 / 3 : ℂ) + (-1 : ℂ) * w) * e010 + ((-1 : ℂ) + (-4 / 3 : ℂ) * w) * e020 + ((1 / 3 : ℂ) + (0 : ℂ) * w) * e100 + ((1 : ℂ) + (2 / 3 : ℂ) * w) * e101 + ((-4 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e103 + ((-4 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e110 + ((-1 : ℂ) + (0 : ℂ) * w) * e201 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e210 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e211 + ((1 / 9 : ℂ) * Y 0 0 + (-2 / 9 : ℂ) * Y 0 1 + (-8 / 9 : ℂ) * Y 0 2 + (-1 / 3 : ℂ) * Y 1 0 + (-1 / 9 : ℂ) * Y 1 1 + (-1 : ℂ) * Y 1 2 + (-2 / 9 : ℂ) * Y 1 3 + (-4 / 9 : ℂ) * Y 2 0 + (2 / 9 : ℂ) * Y 2 1 + (-2 / 9 : ℂ) * Y 2 3 + (2 / 9 : ℂ) * Y 3 0 + (1 / 3 : ℂ) * Y 3 1 + (4 / 3 : ℂ) * Y 3 2) * hw
  have z33 : Y 3 3 = Y 0 0 := by
    linear_combination ((1 : ℂ) + (1 / 3 : ℂ) * w) * e000 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e001 + ((1 : ℂ) + (2 : ℂ) * w) * e003 + ((-2 / 3 : ℂ) + (1 : ℂ) * w) * e010 + ((0 : ℂ) + (1 / 3 : ℂ) * w) * e020 + ((-1 / 3 : ℂ) + (0 : ℂ) * w) * e100 + ((0 : ℂ) + (-2 / 3 : ℂ) * w) * e101 + ((1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e103 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e110 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e201 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e203 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e210 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e211 + ((-16 / 9 : ℂ) * Y 0 0 + (-4 / 9 : ℂ) * Y 0 1 + (-1 / 9 : ℂ) * Y 0 2 + (-1 / 3 : ℂ) * Y 1 0 + (4 / 9 : ℂ) * Y 1 1 + (-10 / 9 : ℂ) * Y 1 3 + (-2 / 9 : ℂ) * Y 2 0 + (1 / 9 : ℂ) * Y 2 1 + (-1 / 9 : ℂ) * Y 2 3 + (4 / 9 : ℂ) * Y 3 0 + (-1 / 3 : ℂ) * Y 3 1 + (4 / 3 : ℂ) * Y 3 3) * hw
  ext i j
  fin_cases i <;> fin_cases j <;> simp [*]

/-- A matrix intertwining the printed generators with their conjugates `ω ↦ -1 - ω` is zero.
Source: Serre, *Linear Representations of Finite Groups*, §2.2 (Schur's lemma) and §2.6 (the
representation is not isomorphic to its conjugate); the exact linear relations are checked below
over `ℚ(ω)`. -/
theorem b63l_schur_zero (w : ℂ) (hw : w ^ 2 + w + 1 = 0) (Y : Matrix (Fin 4) (Fin 4) ℂ)
    (h0 : g32R1 w * Y = Y * g32R1 (-1 - w)) (h1 : g32R2 w * Y = Y * g32R2 (-1 - w))
    (h2 : g32X w * Y = Y * g32X (-1 - w)) :
    Y = 0 := by
  have e000 : (w + 2) / 3 * Y 0 0 + (2 * w + 1) / 3 * Y 1 0 + 0 * Y 2 0 + -((2 * w + 1) / 3) * Y 3 0 = Y 0 0 * (((-1 - w) + 2) / 3) + Y 0 1 * (-(((-1 - w) + 2) / 3)) + Y 0 2 * (0) + Y 0 3 * (((-1 - w) + 2) / 3) := by
    have h' := congrFun (congrFun h0 0) 0
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e001 : (w + 2) / 3 * Y 0 1 + (2 * w + 1) / 3 * Y 1 1 + 0 * Y 2 1 + -((2 * w + 1) / 3) * Y 3 1 = Y 0 0 * ((2 * (-1 - w) + 1) / 3) + Y 0 1 * (((-1 - w) + 2) / 3) + Y 0 2 * (0) + Y 0 3 * ((1 - (-1 - w)) / 3) := by
    have h' := congrFun (congrFun h0 0) 1
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e002 : (w + 2) / 3 * Y 0 2 + (2 * w + 1) / 3 * Y 1 2 + 0 * Y 2 2 + -((2 * w + 1) / 3) * Y 3 2 = Y 0 0 * (0) + Y 0 1 * (0) + Y 0 2 * (1) + Y 0 3 * (0) := by
    have h' := congrFun (congrFun h0 0) 2
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e003 : (w + 2) / 3 * Y 0 3 + (2 * w + 1) / 3 * Y 1 3 + 0 * Y 2 3 + -((2 * w + 1) / 3) * Y 3 3 = Y 0 0 * (-((2 * (-1 - w) + 1) / 3)) + Y 0 1 * ((1 - (-1 - w)) / 3) + Y 0 2 * (0) + Y 0 3 * (((-1 - w) + 2) / 3) := by
    have h' := congrFun (congrFun h0 0) 3
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e010 : -((w + 2) / 3) * Y 0 0 + (w + 2) / 3 * Y 1 0 + 0 * Y 2 0 + (1 - w) / 3 * Y 3 0 = Y 1 0 * (((-1 - w) + 2) / 3) + Y 1 1 * (-(((-1 - w) + 2) / 3)) + Y 1 2 * (0) + Y 1 3 * (((-1 - w) + 2) / 3) := by
    have h' := congrFun (congrFun h0 1) 0
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e020 : 0 * Y 0 0 + 0 * Y 1 0 + 1 * Y 2 0 + 0 * Y 3 0 = Y 2 0 * (((-1 - w) + 2) / 3) + Y 2 1 * (-(((-1 - w) + 2) / 3)) + Y 2 2 * (0) + Y 2 3 * (((-1 - w) + 2) / 3) := by
    have h' := congrFun (congrFun h0 2) 0
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e030 : (w + 2) / 3 * Y 0 0 + (1 - w) / 3 * Y 1 0 + 0 * Y 2 0 + (w + 2) / 3 * Y 3 0 = Y 3 0 * (((-1 - w) + 2) / 3) + Y 3 1 * (-(((-1 - w) + 2) / 3)) + Y 3 2 * (0) + Y 3 3 * (((-1 - w) + 2) / 3) := by
    have h' := congrFun (congrFun h0 3) 0
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e100 : (1 - w) / 3 * Y 0 0 + (2 * w + 1) / 3 * Y 1 0 + (2 * w + 1) / 3 * Y 2 0 + 0 * Y 3 0 = Y 0 0 * ((1 - (-1 - w)) / 3) + Y 0 1 * ((1 - (-1 - w)) / 3) + Y 0 2 * ((1 - (-1 - w)) / 3) + Y 0 3 * (0) := by
    have h' := congrFun (congrFun h1 0) 0
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e101 : (1 - w) / 3 * Y 0 1 + (2 * w + 1) / 3 * Y 1 1 + (2 * w + 1) / 3 * Y 2 1 + 0 * Y 3 1 = Y 0 0 * ((2 * (-1 - w) + 1) / 3) + Y 0 1 * ((1 - (-1 - w)) / 3) + Y 0 2 * (-(((-1 - w) + 2) / 3)) + Y 0 3 * (0) := by
    have h' := congrFun (congrFun h1 0) 1
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e102 : (1 - w) / 3 * Y 0 2 + (2 * w + 1) / 3 * Y 1 2 + (2 * w + 1) / 3 * Y 2 2 + 0 * Y 3 2 = Y 0 0 * ((2 * (-1 - w) + 1) / 3) + Y 0 1 * (-(((-1 - w) + 2) / 3)) + Y 0 2 * ((1 - (-1 - w)) / 3) + Y 0 3 * (0) := by
    have h' := congrFun (congrFun h1 0) 2
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e103 : (1 - w) / 3 * Y 0 3 + (2 * w + 1) / 3 * Y 1 3 + (2 * w + 1) / 3 * Y 2 3 + 0 * Y 3 3 = Y 0 0 * (0) + Y 0 1 * (0) + Y 0 2 * (0) + Y 0 3 * (1) := by
    have h' := congrFun (congrFun h1 0) 3
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e110 : (1 - w) / 3 * Y 0 0 + (1 - w) / 3 * Y 1 0 + -((w + 2) / 3) * Y 2 0 + 0 * Y 3 0 = Y 1 0 * ((1 - (-1 - w)) / 3) + Y 1 1 * ((1 - (-1 - w)) / 3) + Y 1 2 * ((1 - (-1 - w)) / 3) + Y 1 3 * (0) := by
    have h' := congrFun (congrFun h1 1) 0
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e201 : -1 * Y 0 1 + 0 * Y 1 1 + 0 * Y 2 1 + 0 * Y 3 1 = Y 0 0 * (0) + Y 0 1 * (-(((-1 - w) + 2) / 3)) + Y 0 2 * (((-1 - w) + 2) / 3) + Y 0 3 * (-(((-1 - w) + 2) / 3)) := by
    have h' := congrFun (congrFun h2 0) 1
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e203 : -1 * Y 0 3 + 0 * Y 1 3 + 0 * Y 2 3 + 0 * Y 3 3 = Y 0 0 * (0) + Y 0 1 * ((1 - (-1 - w)) / 3) + Y 0 2 * (((-1 - w) + 2) / 3) + Y 0 3 * ((2 * (-1 - w) + 1) / 3) := by
    have h' := congrFun (congrFun h2 0) 3
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e210 : 0 * Y 0 0 + -((w + 2) / 3) * Y 1 0 + -((2 * w + 1) / 3) * Y 2 0 + (1 - w) / 3 * Y 3 0 = Y 1 0 * (-1) + Y 1 1 * (0) + Y 1 2 * (0) + Y 1 3 * (0) := by
    have h' := congrFun (congrFun h2 1) 0
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have e211 : 0 * Y 0 1 + -((w + 2) / 3) * Y 1 1 + -((2 * w + 1) / 3) * Y 2 1 + (1 - w) / 3 * Y 3 1 = Y 1 0 * (0) + Y 1 1 * (-(((-1 - w) + 2) / 3)) + Y 1 2 * (((-1 - w) + 2) / 3) + Y 1 3 * (-(((-1 - w) + 2) / 3)) := by
    have h' := congrFun (congrFun h2 1) 1
    rwa [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h'
  have z00 : Y 0 0 = 0 := by
    linear_combination ((4 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e000 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e001 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e003 + ((-1 : ℂ) + (0 : ℂ) * w) * e010 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e020 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e030 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e100 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e101 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e103 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e201 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e203 + ((1 / 3 : ℂ) * Y 0 0 + (-1 / 3 : ℂ) * Y 0 1 + (-1 / 3 : ℂ) * Y 0 3 + (-1 / 3 : ℂ) * Y 1 0 + (2 / 3 : ℂ) * Y 1 1 + (-2 / 3 : ℂ) * Y 1 3 + (1 / 3 : ℂ) * Y 2 0 + (1 / 3 : ℂ) * Y 2 1 + (-1 / 3 : ℂ) * Y 2 3 + (2 / 3 : ℂ) * Y 3 0 + (-1 / 3 : ℂ) * Y 3 1 + (1 / 3 : ℂ) * Y 3 3) * hw
  have z01 : Y 0 1 = 0 := by
    linear_combination ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e000 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e010 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e020 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e100 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e101 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e103 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e201 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e203 + ((1 / 3 : ℂ) * Y 0 1 + (-1 / 3 : ℂ) * Y 0 2) * hw
  have z02 : Y 0 2 = 0 := by
    linear_combination ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e000 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e010 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e020 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e100 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e101 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e103 + ((-1 : ℂ) + (-1 : ℂ) * w) * e201 + ((1 / 3 : ℂ) * Y 0 0 + (2 / 3 : ℂ) * Y 0 2 + (-1 / 3 : ℂ) * Y 0 3 + (-1 / 3 : ℂ) * Y 1 1 + (1 / 3 : ℂ) * Y 1 3 + (-1 / 3 : ℂ) * Y 2 0 + (-1 / 3 : ℂ) * Y 2 1 + (1 / 3 : ℂ) * Y 2 3 + (-1 / 3 : ℂ) * Y 3 0) * hw
  have z03 : Y 0 3 = 0 := by
    linear_combination ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e201 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e203 + ((1 / 3 : ℂ) * Y 0 3) * hw
  have z10 : Y 1 0 = 0 := by
    linear_combination ((-4 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e000 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e001 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e003 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e010 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e020 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e030 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e100 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e101 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e103 + ((1 : ℂ) + (0 : ℂ) * w) * e210 + ((1 / 3 : ℂ) * Y 0 0 + (2 / 3 : ℂ) * Y 0 1 + (1 / 3 : ℂ) * Y 0 2 + (-1 / 3 : ℂ) * Y 0 3 + (2 / 3 : ℂ) * Y 1 0 + (-1 / 3 : ℂ) * Y 1 1 + (1 / 3 : ℂ) * Y 1 3 + (-1 / 3 : ℂ) * Y 2 0 + (-1 / 3 : ℂ) * Y 2 1 + (1 / 3 : ℂ) * Y 2 3 + (-1 : ℂ) * Y 3 0) * hw
  have z11 : Y 1 1 = 0 := by
    linear_combination ((-1 / 3 : ℂ) + (0 : ℂ) * w) * e000 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e001 + ((1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e010 + ((-1 / 3 : ℂ) + (0 : ℂ) * w) * e020 + ((0 : ℂ) + (-1 / 3 : ℂ) * w) * e100 + ((1 / 3 : ℂ) + (0 : ℂ) * w) * e101 + ((1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e103 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e110 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e210 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e211 + ((4 / 9 : ℂ) * Y 0 0 + (1 / 3 : ℂ) * Y 0 1 + (-1 / 9 : ℂ) * Y 0 2 + (-1 / 9 : ℂ) * Y 0 3 + (8 / 9 : ℂ) * Y 1 1 + (-2 / 9 : ℂ) * Y 1 3 + (-1 / 9 : ℂ) * Y 2 0 + (2 / 9 : ℂ) * Y 2 1 + (-2 / 9 : ℂ) * Y 2 3 + (-1 / 9 : ℂ) * Y 3 0 + (-1 / 3 : ℂ) * Y 3 1) * hw
  have z12 : Y 1 2 = 0 := by
    linear_combination ((-1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e000 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e001 + ((0 : ℂ) + (1 / 3 : ℂ) * w) * e010 + ((2 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e020 + ((1 / 3 : ℂ) + (1 : ℂ) * w) * e100 + ((-2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e101 + ((0 : ℂ) + (-2 / 3 : ℂ) * w) * e103 + ((-2 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e110 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e210 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e211 + ((5 / 9 : ℂ) * Y 0 0 + (4 / 9 : ℂ) * Y 0 2 + (1 / 9 : ℂ) * Y 0 3 + (-1 / 3 : ℂ) * Y 1 0 + (-5 / 9 : ℂ) * Y 1 1 + (1 / 3 : ℂ) * Y 1 2 + (2 / 9 : ℂ) * Y 1 3 + (-8 / 9 : ℂ) * Y 2 0 + (-2 / 9 : ℂ) * Y 2 1 + (2 / 9 : ℂ) * Y 2 3 + (-2 / 9 : ℂ) * Y 3 0 + (1 / 3 : ℂ) * Y 3 1) * hw
  have z13 : Y 1 3 = 0 := by
    linear_combination ((0 : ℂ) + (-1 / 3 : ℂ) * w) * e000 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e003 + ((-2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e010 + ((0 : ℂ) + (2 / 3 : ℂ) * w) * e020 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e030 + ((1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e100 + ((0 : ℂ) + (1 / 3 : ℂ) * w) * e101 + ((2 / 3 : ℂ) + (0 : ℂ) * w) * e103 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e110 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e210 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e211 + ((1 / 9 : ℂ) * Y 0 0 + (2 / 9 : ℂ) * Y 0 2 + (5 / 9 : ℂ) * Y 0 3 + (2 / 9 : ℂ) * Y 1 1 + (4 / 9 : ℂ) * Y 1 3 + (-1 / 9 : ℂ) * Y 2 0 + (2 / 9 : ℂ) * Y 2 1 + (-2 / 9 : ℂ) * Y 2 3 + (2 / 9 : ℂ) * Y 3 0 + (-1 / 3 : ℂ) * Y 3 3) * hw
  have z20 : Y 2 0 = 0 := by
    linear_combination ((2 : ℂ) + (1 : ℂ) * w) * e000 + ((-1 : ℂ) + (0 : ℂ) * w) * e001 + ((1 : ℂ) + (0 : ℂ) * w) * e003 + ((-1 : ℂ) + (0 : ℂ) * w) * e010 + ((-1 : ℂ) + (-1 : ℂ) * w) * e020 + ((0 : ℂ) + (-1 : ℂ) * w) * e030 + ((-1 : ℂ) + (-2 : ℂ) * w) * e100 + ((0 : ℂ) + (-1 : ℂ) * w) * e101 + ((0 : ℂ) + (1 : ℂ) * w) * e103 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e201 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e203 + ((-1 : ℂ) + (0 : ℂ) * w) * e210 + ((-1 : ℂ) * Y 0 0 + (-1 : ℂ) * Y 0 1 + (-1 : ℂ) * Y 0 2 + (-1 / 3 : ℂ) * Y 0 3 + (1 / 3 : ℂ) * Y 1 0 + (2 / 3 : ℂ) * Y 1 1 + (-2 / 3 : ℂ) * Y 1 3 + (5 / 3 : ℂ) * Y 2 0 + (1 / 3 : ℂ) * Y 2 1 + (-1 / 3 : ℂ) * Y 2 3 + (4 / 3 : ℂ) * Y 3 0 + (-1 / 3 : ℂ) * Y 3 1 + (1 / 3 : ℂ) * Y 3 3) * hw
  have z21 : Y 2 1 = 0 := by
    linear_combination ((-1 : ℂ) + (-5 / 3 : ℂ) * w) * e000 + ((1 : ℂ) + (1 : ℂ) * w) * e001 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e003 + ((5 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e010 + ((2 : ℂ) + (4 / 3 : ℂ) * w) * e020 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e030 + ((-4 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e100 + ((-1 : ℂ) + (-1 / 3 : ℂ) * w) * e101 + ((-2 / 3 : ℂ) + (-2 : ℂ) * w) * e103 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e110 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e201 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e203 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e210 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e211 + ((8 / 9 : ℂ) * Y 0 0 + (-1 : ℂ) * Y 0 1 + (-2 / 9 : ℂ) * Y 0 2 + (1 / 9 : ℂ) * Y 0 3 + (1 / 3 : ℂ) * Y 1 0 + (-5 / 9 : ℂ) * Y 1 1 + (11 / 9 : ℂ) * Y 1 3 + (-5 / 9 : ℂ) * Y 2 0 + (4 / 9 : ℂ) * Y 2 1 + (8 / 9 : ℂ) * Y 2 3 + (-8 / 9 : ℂ) * Y 3 0 + (2 / 3 : ℂ) * Y 3 1 + (-1 / 3 : ℂ) * Y 3 3) * hw
  have z22 : Y 2 2 = 0 := by
    linear_combination ((-1 : ℂ) + (-1 / 3 : ℂ) * w) * e000 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e001 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e003 + ((1 : ℂ) + (-1 / 3 : ℂ) * w) * e010 + ((0 : ℂ) + (-1 / 3 : ℂ) * w) * e020 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e030 + ((-2 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e100 + ((1 : ℂ) + (1 / 3 : ℂ) * w) * e101 + ((-1 : ℂ) + (-2 : ℂ) * w) * e102 + ((-1 / 3 : ℂ) + (0 : ℂ) * w) * e103 + ((2 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e110 + ((-1 : ℂ) + (0 : ℂ) * w) * e201 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e210 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e211 + ((4 / 9 : ℂ) * Y 0 0 + (-2 / 3 : ℂ) * Y 0 1 + (-13 / 9 : ℂ) * Y 0 2 + (2 / 9 : ℂ) * Y 0 3 + (2 / 3 : ℂ) * Y 1 0 + (-1 / 9 : ℂ) * Y 1 1 + (1 : ℂ) * Y 1 2 + (4 / 9 : ℂ) * Y 1 3 + (5 / 9 : ℂ) * Y 2 0 + (-1 / 9 : ℂ) * Y 2 1 + (4 / 3 : ℂ) * Y 2 2 + (1 / 9 : ℂ) * Y 2 3 + (-4 / 9 : ℂ) * Y 3 0 + (-1 / 3 : ℂ) * Y 3 3) * hw
  have z23 : Y 2 3 = 0 := by
    linear_combination ((0 : ℂ) + (1 / 3 : ℂ) * w) * e000 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e003 + ((2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e010 + ((0 : ℂ) + (-2 / 3 : ℂ) * w) * e020 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e030 + ((-1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e100 + ((0 : ℂ) + (-1 / 3 : ℂ) * w) * e101 + ((-5 / 3 : ℂ) + (-2 : ℂ) * w) * e103 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e110 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e201 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e203 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e210 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e211 + ((-1 / 9 : ℂ) * Y 0 0 + (-2 / 9 : ℂ) * Y 0 2 + (-14 / 9 : ℂ) * Y 0 3 + (-2 / 9 : ℂ) * Y 1 1 + (8 / 9 : ℂ) * Y 1 3 + (1 / 9 : ℂ) * Y 2 0 + (-2 / 9 : ℂ) * Y 2 1 + (14 / 9 : ℂ) * Y 2 3 + (-2 / 9 : ℂ) * Y 3 0 + (1 / 3 : ℂ) * Y 3 3) * hw
  have z30 : Y 3 0 = 0 := by
    linear_combination ((1 / 3 : ℂ) + (5 / 3 : ℂ) * w) * e000 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e001 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e003 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e010 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e020 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e030 + ((4 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e100 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e101 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e103 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e201 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e203 + ((1 : ℂ) + (0 : ℂ) * w) * e210 + ((-1 / 3 : ℂ) * Y 0 0 + (4 / 3 : ℂ) * Y 0 1 + (2 / 3 : ℂ) * Y 0 2 + (-1 : ℂ) * Y 0 3 + (-1 : ℂ) * Y 1 0 + (-1 / 3 : ℂ) * Y 2 0 + (-1 / 3 : ℂ) * Y 2 1 + (1 / 3 : ℂ) * Y 2 3 + (2 / 3 : ℂ) * Y 3 0 + (-1 / 3 : ℂ) * Y 3 1 + (1 / 3 : ℂ) * Y 3 3) * hw
  have z31 : Y 3 1 = 0 := by
    linear_combination ((4 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e000 + ((0 : ℂ) + (1 : ℂ) * w) * e001 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e003 + ((-1 / 3 : ℂ) + (1 : ℂ) * w) * e010 + ((-2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e020 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e030 + ((-1 / 3 : ℂ) + (-1 : ℂ) * w) * e100 + ((-1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e101 + ((1 : ℂ) + (2 / 3 : ℂ) * w) * e103 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e110 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e201 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e203 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e210 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e211 + ((-5 / 9 : ℂ) * Y 0 0 + (-1 : ℂ) * Y 0 1 + (-4 / 9 : ℂ) * Y 0 2 + (5 / 9 : ℂ) * Y 0 3 + (-1 / 3 : ℂ) * Y 1 0 + (2 / 9 : ℂ) * Y 1 1 + (-8 / 9 : ℂ) * Y 1 3 + (2 / 9 : ℂ) * Y 2 0 + (5 / 9 : ℂ) * Y 2 1 + (-5 / 9 : ℂ) * Y 2 3 + (5 / 9 : ℂ) * Y 3 0 + (2 / 3 : ℂ) * Y 3 1 + (1 / 3 : ℂ) * Y 3 3) * hw
  have z32 : Y 3 2 = 0 := by
    linear_combination ((-2 / 3 : ℂ) + (-1 : ℂ) * w) * e000 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e001 + ((1 : ℂ) + (2 : ℂ) * w) * e002 + ((2 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e010 + ((4 / 3 : ℂ) + (1 : ℂ) * w) * e020 + ((0 : ℂ) + (4 / 3 : ℂ) * w) * e100 + ((-1 / 3 : ℂ) + (1 : ℂ) * w) * e101 + ((-1 / 3 : ℂ) + (-4 / 3 : ℂ) * w) * e103 + ((-2 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e110 + ((0 : ℂ) + (-1 : ℂ) * w) * e201 + ((1 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e210 + ((-2 / 3 : ℂ) + (-1 / 3 : ℂ) * w) * e211 + ((8 / 9 : ℂ) * Y 0 0 + (4 / 9 : ℂ) * Y 0 2 + (-2 / 9 : ℂ) * Y 0 3 + (-1 / 3 : ℂ) * Y 1 0 + (-8 / 9 : ℂ) * Y 1 1 + (-1 : ℂ) * Y 1 2 + (5 / 9 : ℂ) * Y 1 3 + (-11 / 9 : ℂ) * Y 2 0 + (-5 / 9 : ℂ) * Y 2 1 + (5 / 9 : ℂ) * Y 2 3 + (-5 / 9 : ℂ) * Y 3 0 + (1 / 3 : ℂ) * Y 3 1 + (4 / 3 : ℂ) * Y 3 2) * hw
  have z33 : Y 3 3 = 0 := by
    linear_combination ((-1 : ℂ) + (-1 / 3 : ℂ) * w) * e000 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e001 + ((0 : ℂ) + (1 : ℂ) * w) * e003 + ((-1 / 3 : ℂ) + (0 : ℂ) * w) * e010 + ((0 : ℂ) + (2 / 3 : ℂ) * w) * e020 + ((-1 : ℂ) + (0 : ℂ) * w) * e030 + ((1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e100 + ((0 : ℂ) + (1 / 3 : ℂ) * w) * e101 + ((2 / 3 : ℂ) + (0 : ℂ) * w) * e103 + ((-1 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e110 + ((1 / 3 : ℂ) + (2 / 3 : ℂ) * w) * e201 + ((-1 / 3 : ℂ) + (-2 / 3 : ℂ) * w) * e203 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e210 + ((2 / 3 : ℂ) + (1 / 3 : ℂ) * w) * e211 + ((7 / 9 : ℂ) * Y 0 0 + (1 / 3 : ℂ) * Y 0 1 + (2 / 9 : ℂ) * Y 0 2 + (2 / 9 : ℂ) * Y 0 3 + (1 / 3 : ℂ) * Y 1 0 + (-1 / 9 : ℂ) * Y 1 1 + (-5 / 9 : ℂ) * Y 1 3 + (-1 / 9 : ℂ) * Y 2 0 + (2 / 9 : ℂ) * Y 2 1 + (-2 / 9 : ℂ) * Y 2 3 + (-1 / 9 : ℂ) * Y 3 0 + (1 / 3 : ℂ) * Y 3 1 + (2 / 3 : ℂ) * Y 3 3) * hw
  ext i j
  fin_cases i <;> fin_cases j <;> simp [*]

noncomputable section

local notation "ρ" => b4b_toMatrix

theorem b63l_omega_re : g32h_omega.re = -(1 / 2 : ℝ) := by
  have harg : 2 * Real.pi * Complex.I / 3 = (2 * Real.pi / 3 : ℝ) * Complex.I := by
    push_cast
    ring
  rw [g32h_omega, harg, Complex.exp_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.mul_im,
    Complex.ofReal_im, Complex.I_im, mul_one, add_zero]
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_sub]
  rw [Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]
  norm_num

theorem b63l_conj_omega : starRingEnd ℂ g32h_omega = -1 - g32h_omega := by
  apply Complex.ext
  · simp [b63l_omega_re]
    norm_num
  · simp

theorem b63l_card_group : Fintype.card b4b_Group = 155520 := by
  rw [Fintype.card_eq_nat_card]
  exact (Nat.card_coe_set_eq (g32h_G : Set (Matrix (Fin 4) (Fin 4) ℂ))).trans
    HurwitzPrymRex_g32_ncard

theorem b63l_toMatrix_entry_inv (g : b4b_Group) (i j : Fin 4) :
    ρ g⁻¹ i j = starRingEnd ℂ (ρ g j i) := by
  rw [b63l_toMatrix_inv_eq_star]
  rfl

theorem b63l_transpose_map_star (g : b4b_Group) :
    (ρ g)ᵀ * (ρ g).map star = 1 := by
  have h : star (ρ g) * ρ g = 1 := by
    rw [← b63l_toMatrix_inv_eq_star, ← map_mul, inv_mul_cancel, map_one]
  have h' := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_one] at h'
  rw [← h']
  rfl

/-- The group average `∑ ρ(g) X ρ(g)⁻¹` is the scalar `|G| tr X / 4`.
Source: Serre, *Linear Representations of Finite Groups*, §2.2, Proposition 4 and its
corollaries. -/
theorem b63l_average_scalar (X : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ g : b4b_Group, ρ g * X * ρ g⁻¹ =
      ((155520 : ℂ) / 4 * X.trace) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  set T := ∑ g : b4b_Group, ρ g * X * ρ g⁻¹ with hT
  have hcomm (h : b4b_Group) : ρ h * T = T * ρ h := by
    rw [hT, Finset.mul_sum, Finset.sum_mul]
    conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft h)]
    apply Finset.sum_congr rfl
    intro g _
    have key : ρ (h * g)⁻¹ * ρ h = ρ g⁻¹ := by
      rw [← map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    show ρ h * (ρ g * X * ρ g⁻¹) = ρ (h * g) * X * ρ (h * g)⁻¹ * ρ h
    rw [Matrix.mul_assoc (ρ (h * g) * X), key, map_mul]
    simp only [Matrix.mul_assoc]
  have hs := b63l_schur_scalar g32h_omega g32h_omega_sq_add T (hcomm (b4b_generators 0))
    (hcomm (b4b_generators 1)) (hcomm (b4b_generators 2))
  have htr : T.trace = 155520 * X.trace := by
    rw [hT, Matrix.trace_sum]
    have (g : b4b_Group) : (ρ g * X * ρ g⁻¹).trace = X.trace := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one,
        Matrix.one_mul]
    simp only [this, Finset.sum_const, Finset.card_univ, b63l_card_group, nsmul_eq_mul]
    norm_num
  have h4 : T.trace = 4 * T 0 0 := by
    conv_lhs => rw [hs]
    simp [Matrix.trace_smul]
    ring
  rw [hs]
  congr 1
  linear_combination (-1 / 4 : ℂ) * h4 + (1 / 4 : ℂ) * htr

theorem b63l_gen_map_star (k : Fin 4) :
    (ρ (b4b_generators k)).map star =
      ![g32R1 (-1 - g32h_omega), g32R2 (-1 - g32h_omega), g32X (-1 - g32h_omega),
        g32Y (-1 - g32h_omega)] k := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [b4b_generators, b4b_toMatrix, g32R1, g32R2, g32X, g32Y, Matrix.map_apply,
      b63l_conj_omega, map_ofNat]

/-- The group average `∑ ρ(g) X ρ(g)ᵀ` vanishes.
Source: Serre, *Linear Representations of Finite Groups*, §2.2, Proposition 4 (applied to the
non-isomorphic representations `ρ` and its conjugate). -/
theorem b63l_average_zero (X : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ g : b4b_Group, ρ g * X * (ρ g)ᵀ = 0 := by
  set B := ∑ g : b4b_Group, ρ g * X * (ρ g)ᵀ with hB
  have hinv (h : b4b_Group) : ρ h * B * (ρ h)ᵀ = B := by
    rw [hB, Finset.mul_sum, Finset.sum_mul]
    conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft h)]
    apply Finset.sum_congr rfl
    intro g _
    rw [Equiv.coe_mulLeft, map_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  have hcomm (h : b4b_Group) : ρ h * B = B * (ρ h).map star := by
    calc ρ h * B = ρ h * B * ((ρ h)ᵀ * (ρ h).map star) := by
          rw [b63l_transpose_map_star, Matrix.mul_one]
      _ = B * (ρ h).map star := by
          rw [← Matrix.mul_assoc, hinv]
  have h0 := hcomm (b4b_generators 0)
  have h1 := hcomm (b4b_generators 1)
  have h2 := hcomm (b4b_generators 2)
  rw [b63l_gen_map_star 0] at h0
  rw [b63l_gen_map_star 1] at h1
  rw [b63l_gen_map_star 2] at h2
  exact b63l_schur_zero g32h_omega g32h_omega_sq_add B h0 h1 h2

end

end HodgeLean.Foundations.Program
