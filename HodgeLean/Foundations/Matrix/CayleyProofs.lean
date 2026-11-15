import HodgeLean.Foundations.Matrix.CayleyDefs
import Mathlib.Tactic

/-! # Matrix Cayley proof bodies

HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.MatrixCayley
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Rational matrix Cayley identity.
Source: Weyl, The Classical Groups, Chapter II, §10;
`docs/specs/HeckeSpreading.md`, S1; `Program.hk_cayley_mem_unitary`. -/
theorem preservesForm_aux {K : Type*} [Field K] [StarRing K] {H X : Matrix n n K} (hX : Xᴴ * H + H * X = 0) (hd : (1 + X).det ≠ 0) :
    (cayley X)ᴴ * H * cayley X = H := by
  set A := 1 + X with hA
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hd
  have hBu : IsUnit Aᴴ.det := by
    rw [Matrix.det_conjTranspose]; exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hd)
  have h1 : (1 - X)ᴴ * H = H * A := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.sub_mul, hA, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one]
    rw [← sub_eq_zero]
    rw [show H - Xᴴ * H - (H + H * X) = -(Xᴴ * H + H * X) by abel, hX, neg_zero]
  have h2 : H * (1 - X) = Aᴴ * H := by
    rw [hA, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.mul_sub, Matrix.add_mul,
      Matrix.one_mul, Matrix.mul_one]
    rw [← sub_eq_zero]
    rw [show H - H * X - (H + Xᴴ * H) = -(Xᴴ * H + H * X) by abel, hX, neg_zero]
  have hc : A * (1 - X) = (1 - X) * A := by
    rw [hA]; noncomm_ring
  unfold cayley
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, ← hA]
  calc Aᴴ⁻¹ * (1 - X)ᴴ * H * ((1 - X) * A⁻¹)
      = Aᴴ⁻¹ * ((1 - X)ᴴ * H) * (1 - X) * A⁻¹ := by simp only [Matrix.mul_assoc]
    _ = Aᴴ⁻¹ * H * (A * (1 - X)) * A⁻¹ := by rw [h1]; simp only [Matrix.mul_assoc]
    _ = Aᴴ⁻¹ * (H * (1 - X)) * (A * A⁻¹) := by rw [hc]; simp only [Matrix.mul_assoc]
    _ = H := by
      rw [h2, Matrix.mul_nonsing_inv _ hAu, Matrix.mul_one, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hBu, Matrix.one_mul]

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
theorem skewAdjoint_aux {K : Type*} [Field K] [StarRing K] {H g : Matrix n n K} (hg : gᴴ * H * g = H) (hd : (1 + g).det ≠ 0) :
    (cayley g)ᴴ * H + H * cayley g = 0 := by
  set A := 1 + g with hA
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hd
  have hBu : IsUnit Aᴴ.det := by
    rw [Matrix.det_conjTranspose]; exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hd)
  unfold cayley
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, ← hA]
  clear_value A
  have key : Aᴴ * (Aᴴ⁻¹ * (1 - g)ᴴ * H + H * ((1 - g) * A⁻¹)) * A = 0 := by
    have e1 : Aᴴ * (Aᴴ⁻¹ * (1 - g)ᴴ * H) * A = (1 - g)ᴴ * H * A := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBu, Matrix.one_mul,
        Matrix.mul_assoc]
    have e2 : Aᴴ * (H * ((1 - g) * A⁻¹)) * A = Aᴴ * H * (1 - g) := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu, Matrix.mul_one]
    rw [Matrix.mul_add, Matrix.add_mul, e1, e2, hA, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_add, Matrix.conjTranspose_one]
    have : (1 - gᴴ) * H * (1 + g) + (1 + gᴴ) * H * (1 - g) = 2 * (H - gᴴ * H * g) := by
      noncomm_ring
    rw [this, hg, sub_self, mul_zero]
  set M := Aᴴ⁻¹ * (1 - g)ᴴ * H + H * ((1 - g) * A⁻¹)
  calc M = Aᴴ⁻¹ * Aᴴ * M * (A * A⁻¹) := by
        rw [Matrix.nonsing_inv_mul _ hBu, Matrix.mul_nonsing_inv _ hAu, Matrix.one_mul,
          Matrix.mul_one]
    _ = Aᴴ⁻¹ * (Aᴴ * M * A) * A⁻¹ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [key, Matrix.mul_zero, Matrix.zero_mul]

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
theorem involution_aux {K : Type*} [Field K] {X : Matrix n n K} (h2 : (2 : K) ≠ 0) (hd : (1 + X).det ≠ 0) :
    (1 + cayley X).det ≠ 0 ∧ cayley (cayley X) = X := by
  have hadd : 1 + cayley X = (2 : K) • (1 + X)⁻¹ := by
    have hAu : IsUnit (1 + X).det := isUnit_iff_ne_zero.mpr hd
    unfold cayley
    calc 1 + (1 - X) * (1 + X)⁻¹ = ((1 + X) + (1 - X)) * (1 + X)⁻¹ := by
          rw [Matrix.add_mul (1 + X), Matrix.mul_nonsing_inv _ hAu]
      _ = (2 : K) • (1 + X)⁻¹ := by
          rw [show (1 + X) + (1 - X) = (2 : K) • (1 : Matrix n n K) by
            rw [two_smul]; abel, Matrix.smul_mul, Matrix.one_mul]
  constructor
  · rw [hadd, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (pow_ne_zero _ h2) (inv_ne_zero hd)
  ·
    have hAu : IsUnit (1 + X).det := isUnit_iff_ne_zero.mpr hd
    have hinv : (1 + cayley X)⁻¹ = (2⁻¹ : K) • (1 + X) := by
      apply Matrix.inv_eq_right_inv
      rw [hadd, Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hAu,
        smul_smul, mul_inv_cancel₀ h2, one_smul]
    have hsub : 1 - cayley X = (2 : K) • (X * (1 + X)⁻¹) := by
      unfold cayley
      calc 1 - (1 - X) * (1 + X)⁻¹ = ((1 + X) - (1 - X)) * (1 + X)⁻¹ := by
            rw [Matrix.sub_mul (1 + X), Matrix.mul_nonsing_inv _ hAu]
        _ = (2 : K) • (X * (1 + X)⁻¹) := by
            rw [show (1 + X) - (1 - X) = (2 : K) • X by rw [two_smul]; abel, Matrix.smul_mul]
    rw [show cayley (cayley X) = (1 - cayley X) * (1 + cayley X)⁻¹ from rfl]
    rw [hsub, hinv, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ h2,
      one_smul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu, Matrix.mul_one]

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
theorem commutes_aux {K : Type*} [Field K] {X Ω : Matrix n n K} (h : X * Ω = Ω * X) :
    cayley X * Ω = Ω * cayley X := by
  have hinv : ∀ {A : Matrix n n K}, A * Ω = Ω * A → A⁻¹ * Ω = Ω * A⁻¹ := by
    intro A h
    by_cases hA : IsUnit A.det
    · calc A⁻¹ * Ω = A⁻¹ * (Ω * A) * A⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]
        _ = A⁻¹ * (A * Ω) * A⁻¹ := by rw [h]
        _ = Ω * A⁻¹ := by
            rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
    · rw [Matrix.nonsing_inv_apply_not_isUnit _ hA, Matrix.zero_mul, Matrix.mul_zero]
  have h1 : (1 + X) * Ω = Ω * (1 + X) := by
    rw [Matrix.add_mul, Matrix.mul_add, h, Matrix.one_mul, Matrix.mul_one]
  have h2 : (1 - X) * Ω = Ω * (1 - X) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, h, Matrix.one_mul, Matrix.mul_one]
  unfold cayley
  rw [Matrix.mul_assoc, hinv h1, ← Matrix.mul_assoc, h2, Matrix.mul_assoc]

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
theorem map_aux {K L : Type*} [Field K] [Field L] (f : K →+* L) (X : Matrix n n K) :
    (cayley X).map f = cayley (X.map f) := by
  have hm : ∀ M : Matrix n n K, M.map f = f.mapMatrix M := fun _ => rfl
  have hinv : ((1 + X)⁻¹).map f = (1 + X.map f)⁻¹ := by
    have e : 1 + X.map f = f.mapMatrix (1 + X) := by rw [map_add, map_one]; rfl
    rw [e]
    by_cases hA : IsUnit (1 + X).det
    · symm
      apply Matrix.inv_eq_left_inv
      rw [hm, ← map_mul, Matrix.nonsing_inv_mul _ hA, map_one]
    · have h0 : (1 + X).det = 0 := by rwa [isUnit_iff_ne_zero, not_not] at hA
      have hA' : ¬ IsUnit (f.mapMatrix (1 + X)).det := by
        rw [← RingHom.map_det, h0, map_zero]; exact not_isUnit_zero
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hA, Matrix.nonsing_inv_apply_not_isUnit _ hA']
      simp
  unfold cayley
  rw [hm, map_mul, map_sub, map_one, ← hm ((1 + X)⁻¹), hinv]
  rfl

example :
    let X : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 0, 1]
    (cayley X).map (algebraMap ℚ ℂ) = !![0, -1/2; 0, 0] ∧
      cayley (X.map (algebraMap ℚ ℂ)) = !![0, -1/2; 0, 0] := by
  norm_num [cayley, Matrix.inv_def, Matrix.adjugate_fin_two, det_fin_two,
    Matrix.mul_fin_two, Matrix.map]
  <;> (repeat' apply And.intro)
  <;> (try ext i j) <;> (try fin_cases i) <;> (try fin_cases j)
  <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct]

end HodgeLean.Foundations.MatrixCayley
