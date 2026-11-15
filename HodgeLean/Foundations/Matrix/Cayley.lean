import HodgeLean.Foundations.Matrix.CayleyProofs

/-! # Matrix Cayley specification

HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.MatrixCayley
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Rational matrix Cayley identity.
Source: Weyl, The Classical Groups, Chapter II, §10;
`docs/specs/HeckeSpreading.md`, S1; `Program.hk_cayley_mem_unitary`. -/
theorem preservesForm {K : Type*} [Field K] [StarRing K] {H X : Matrix n n K} (hX : Xᴴ * H + H * X = 0) (hd : (1 + X).det ≠ 0) :
    (cayley X)ᴴ * H * cayley X = H := preservesForm_aux hX hd

example :
    let X : Matrix (Fin 2) (Fin 2) ℚ := !![0, -1; 1, 0]
    Xᴴ + X = 0 ∧ (1 + X).det = 2 ∧
      cayley X = !![0, 1; -1, 0] ∧ (cayley X)ᴴ * cayley X = 1 := by
  norm_num [cayley, Matrix.inv_def, Matrix.adjugate_fin_two, det_fin_two,
    Matrix.conjTranspose, Matrix.transpose, Matrix.mul_fin_two]
  <;> (repeat' apply And.intro)
  <;> (try ext i j) <;> (try fin_cases i) <;> (try fin_cases j)
  <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct]

/-- Rational matrix Cayley identity.
Source: Weyl, The Classical Groups, Chapter II, §10;
`docs/specs/HeckeSpreading.md`, S1; `Program.hk_cayley_mem_lie`. -/
theorem skewAdjoint {K : Type*} [Field K] [StarRing K] {H g : Matrix n n K} (hg : gᴴ * H * g = H) (hd : (1 + g).det ≠ 0) :
    (cayley g)ᴴ * H + H * cayley g = 0 := skewAdjoint_aux hg hd

example :
    let g : Matrix (Fin 2) (Fin 2) ℚ := !![0, -1; 1, 0]
    gᴴ * g = 1 ∧ (1 + g).det = 2 ∧
      cayley g = !![0, 1; -1, 0] ∧ (cayley g)ᴴ + cayley g = 0 := by
  norm_num [cayley, Matrix.inv_def, Matrix.adjugate_fin_two, det_fin_two,
    Matrix.conjTranspose, Matrix.transpose, Matrix.mul_fin_two]
  <;> (repeat' apply And.intro)
  <;> (try ext i j) <;> (try fin_cases i) <;> (try fin_cases j)
  <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct]

/-- Rational matrix Cayley identity.
Source: Weyl, The Classical Groups, Chapter II, §10;
`docs/specs/HeckeSpreading.md`, S1; `Program.hk_cayley_cayley`. -/
theorem involution {K : Type*} [Field K] {X : Matrix n n K} (h2 : (2 : K) ≠ 0) (hd : (1 + X).det ≠ 0) :
    (1 + cayley X).det ≠ 0 ∧ cayley (cayley X) = X := involution_aux h2 hd

example :
    let X : Matrix (Fin 2) (Fin 2) ℚ := !![2, 0; 0, 3]
    (1 + X).det = 12 ∧ cayley X = !![-1/3, 0; 0, -1/2] ∧
      (1 + cayley X).det = 1/3 ∧ cayley (cayley X) = X := by
  norm_num [cayley, Matrix.inv_def, Matrix.adjugate_fin_two, det_fin_two,
    Matrix.mul_fin_two]
  <;> (repeat' apply And.intro)
  <;> (try ext i j) <;> (try fin_cases i) <;> (try fin_cases j)
  <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct]

/-- Rational matrix Cayley identity.
Source: Weyl, The Classical Groups, Chapter II, §10;
`docs/specs/HeckeSpreading.md`, S1; `Program.hk_cayley_commute`. -/
theorem commutes {K : Type*} [Field K] {X Ω : Matrix n n K} (h : X * Ω = Ω * X) :
    cayley X * Ω = Ω * cayley X := commutes_aux h

example :
    let X : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 0, 1]
    let Ω : Matrix (Fin 2) (Fin 2) ℚ := !![2, 3; 0, 2]
    X * Ω = Ω * X ∧ cayley X = !![0, -1/2; 0, 0] ∧
      cayley X * Ω = Ω * cayley X := by
  norm_num [cayley, Matrix.inv_def, Matrix.adjugate_fin_two, det_fin_two,
    Matrix.mul_fin_two]
  <;> (repeat' apply And.intro)
  <;> (try ext i j) <;> (try fin_cases i) <;> (try fin_cases j)
  <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct]

/-- Rational matrix Cayley identity.
Source: Weyl, The Classical Groups, Chapter II, §10;
`docs/specs/HeckeSpreading.md`, S1; `Program.hk_cayley_map`. -/
theorem map {K L : Type*} [Field K] [Field L] (f : K →+* L) (X : Matrix n n K) :
    (cayley X).map f = cayley (X.map f) := map_aux f X

example :
    let X : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 0, 1]
    (cayley X).map (algebraMap ℚ ℂ) = !![0, -1/2; 0, 0] ∧
      cayley (X.map (algebraMap ℚ ℂ)) = !![0, -1/2; 0, 0] := by
  norm_num [cayley, Matrix.inv_def, Matrix.adjugate_fin_two, det_fin_two,
    Matrix.mul_fin_two, Matrix.map]
  <;> (repeat' apply And.intro)
  <;> (try ext i j) <;> (try fin_cases i) <;> (try fin_cases j)
  <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct]

/-- Rational matrix Cayley identity.
Source: Weyl, The Classical Groups, Chapter II, §10;
`docs/specs/HeckeSpreading.md`, S1; `Program.hk_cayley_cayley`. -/
theorem domain_charZero {K : Type*} [Field K] [CharZero K] {X : Matrix n n K}
    (hd : (1 + X).det ≠ 0) : (1 + cayley X).det ≠ 0 :=
  (involution (by exact_mod_cast (show (2 : ℕ) ≠ 0 by decide)) hd).1

example :
    let X : Matrix (Fin 2) (Fin 2) ℚ := !![2, 0; 0, 3]
    (1 + X).det = 12 ∧ (1 + cayley X).det = 1/3 := by
  norm_num [cayley, Matrix.inv_def, Matrix.adjugate_fin_two, det_fin_two,
    Matrix.mul_fin_two]
  <;> (repeat' apply And.intro)
  <;> (try ext i j) <;> (try fin_cases i) <;> (try fin_cases j)
  <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct]

/-- Rational matrix Cayley identity.
Source: Weyl, The Classical Groups, Chapter II, §10;
`docs/specs/HeckeSpreading.md`, S1; `Program.hk_cayley_cayley`. -/
theorem involution_charZero {K : Type*} [Field K] [CharZero K] {X : Matrix n n K}
    (hd : (1 + X).det ≠ 0) : cayley (cayley X) = X :=
  (involution (by exact_mod_cast (show (2 : ℕ) ≠ 0 by decide)) hd).2

example :
    let X : Matrix (Fin 2) (Fin 2) ℚ := !![2, 0; 0, 3]
    cayley (cayley X) = X := by
  norm_num [cayley, Matrix.inv_def, Matrix.adjugate_fin_two, det_fin_two,
    Matrix.mul_fin_two]
  <;> (repeat' apply And.intro)
  <;> (try ext i j) <;> (try fin_cases i) <;> (try fin_cases j)
  <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct]

end HodgeLean.Foundations.MatrixCayley
