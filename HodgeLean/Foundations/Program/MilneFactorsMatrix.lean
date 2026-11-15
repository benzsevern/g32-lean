import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

namespace HodgeLean.Foundations.Program

open Matrix

variable {n : ℕ} {K : Type*} [Field K]

theorem m1_matrix_column_expansion (X : Matrix (Fin n) (Fin n) K) (j z : Fin n) :
    X * Matrix.single j z 1 = ∑ i, X i j • Matrix.single i z 1 := by
  ext a b
  by_cases h : z = b
  · subst b
    simp [Matrix.mul_apply, Matrix.single, Matrix.sum_apply, Matrix.smul_apply, eq_comm]
  · simp [Matrix.mul_apply, Matrix.single, Matrix.sum_apply, Matrix.smul_apply, h]


theorem m1_matrix_intertwiner (φ : Matrix (Fin n) (Fin n) K ≃ₐ[K]
    Matrix (Fin n) (Fin n) K) (z k : Fin n) (X : Matrix (Fin n) (Fin n) K) :
    φ X * (Matrix.of fun a b => φ (Matrix.single b z 1) a k) =
      (Matrix.of fun a b => φ (Matrix.single b z 1) a k) * X := by
  ext a b
  have h := congrArg (fun Y : Matrix (Fin n) (Fin n) K => φ Y a k)
    (m1_matrix_column_expansion X b z)
  simpa only [map_mul, map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.mul_apply, Matrix.of_apply, mul_comm] using h


theorem m1_matrix_intertwiner_left_product
    (φ : Matrix (Fin n) (Fin n) K ≃ₐ[K] Matrix (Fin n) (Fin n) K)
    (z k l : Fin n) :
    (Matrix.of fun a b => φ (Matrix.single z a 1) l b) *
      (Matrix.of fun a b => φ (Matrix.single b z 1) a k) =
      φ (Matrix.single z z 1) l k • (1 : Matrix (Fin n) (Fin n) K) := by
  ext a b
  change (φ (Matrix.single z a 1) * φ (Matrix.single b z 1)) l k = _
  rw [← map_mul]
  by_cases h : a = b
  · subst b
    simp [Matrix.single_mul_single_same, Matrix.smul_apply]
  · rw [Matrix.single_mul_single_of_ne (1 : K) z a b h 1, map_zero]
    simp [Matrix.smul_apply, h]


theorem m1_matrix_automorphism_inner (φ : Matrix (Fin n) (Fin n) K ≃ₐ[K]
    Matrix (Fin n) (Fin n) K) (z : Fin n) :
    ∃ P : Matrix (Fin n) (Fin n) K, IsUnit P ∧ ∀ X, φ X * P = P * X := by
  have he : φ (Matrix.single z z 1) ≠ 0 := by
    intro h
    have hh := φ.injective (h.trans φ.map_zero.symm)
    have := congrArg (fun Y : Matrix (Fin n) (Fin n) K => Y z z) hh
    simpa using this
  obtain ⟨l, k, hk⟩ : ∃ l k, φ (Matrix.single z z 1) l k ≠ 0 := by
    by_contra h
    push_neg at h
    exact he (Matrix.ext fun l k => h l k)
  let P := Matrix.of fun a b => φ (Matrix.single b z 1) a k
  let Q := Matrix.of fun a b => φ (Matrix.single z a 1) l b
  have hp : Q * P = φ (Matrix.single z z 1) l k • 1 :=
    m1_matrix_intertwiner_left_product φ z k l
  have hu : IsUnit (Q * P) := by
    rw [hp]
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (isUnit_iff_ne_zero.mpr hk).map (algebraMap K (Matrix (Fin n) (Fin n) K))
  exact ⟨P, isUnit_of_mul_isUnit_right hu, m1_matrix_intertwiner φ z k⟩


theorem m1_reversal_one {A : Type*} [Ring A] [Algebra K A]
    (τ : A ≃ₗ[K] A) (hmul : ∀ X Y, τ (X * Y) = τ Y * τ X) : τ 1 = 1 := by
  have h := hmul (τ.symm 1) 1
  simpa only [mul_one, τ.apply_symm_apply, mul_one] using h.symm


theorem m1_reversal_gram_intertwiner
    (τ : Matrix (Fin n) (Fin n) K ≃ₗ[K] Matrix (Fin n) (Fin n) K)
    (hmul : ∀ X Y, τ (X * Y) = τ Y * τ X) (z : Fin n) :
    ∃ B : Matrix (Fin n) (Fin n) K, IsUnit B ∧ ∀ X, B * τ X = X.transpose * B := by
  let e := τ.trans (Matrix.transposeLinearEquiv (Fin n) (Fin n) K K)
  have he1 : e 1 = 1 := by
    change (τ 1).transpose = 1
    rw [m1_reversal_one τ hmul, Matrix.transpose_one]
  have hem : ∀ X Y, e (X * Y) = e X * e Y := by
    intro X Y
    change (τ (X * Y)).transpose = (τ X).transpose * (τ Y).transpose
    rw [hmul, Matrix.transpose_mul]
  let φ := AlgEquiv.ofLinearEquiv e he1 hem
  obtain ⟨P, hP, hp⟩ := m1_matrix_automorphism_inner φ z
  refine ⟨P.transpose, (Matrix.isUnit_transpose P).mpr hP, ?_⟩
  intro X
  have h := congrArg Matrix.transpose (hp X)
  change ((τ X).transpose * P).transpose = (P * X).transpose at h
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using h


theorem m1_gram_transpose_intertwines
    (τ : Matrix (Fin n) (Fin n) K ≃ₗ[K] Matrix (Fin n) (Fin n) K)
    (hτ : Function.Involutive τ) (B : Matrix (Fin n) (Fin n) K)
    (hB : ∀ X, B * τ X = X.transpose * B) (X : Matrix (Fin n) (Fin n) K) :
    B.transpose * τ X = X.transpose * B.transpose := by
  have h := congrArg Matrix.transpose (hB (τ X))
  simpa only [hτ X, Matrix.transpose_mul, Matrix.transpose_transpose] using h.symm


theorem m1_gram_transpose_scalar
    (τ : Matrix (Fin n) (Fin n) K ≃ₗ[K] Matrix (Fin n) (Fin n) K)
    (hτ : Function.Involutive τ) (B : Matrix (Fin n) (Fin n) K) (hu : IsUnit B)
    (hB : ∀ X, B * τ X = X.transpose * B) : ∃ c : K, B.transpose = c • B := by
  have hd := (Matrix.isUnit_iff_isUnit_det B).mp hu
  let C := B⁻¹ * B.transpose
  have hc (X : Matrix (Fin n) (Fin n) K) : C * τ X = τ X * C := by
    calc
      C * τ X = B⁻¹ * (B.transpose * τ X) := mul_assoc _ _ _
      _ = B⁻¹ * (X.transpose * B.transpose) := by rw [m1_gram_transpose_intertwines τ hτ B hB]
      _ = (B⁻¹ * (X.transpose * B)) * C := by
        simp only [C, mul_assoc, Matrix.mul_nonsing_inv_cancel_left B _ hd]
      _ = τ X * C := by rw [← hB, Matrix.nonsing_inv_mul_cancel_left B _ hd]
  obtain ⟨c, hc'⟩ := Matrix.mem_range_scalar_of_commute_single
    (M := C) (fun i j _ => by
      have h := hc (τ.symm (Matrix.single i j 1))
      rw [τ.apply_symm_apply] at h
      exact h.symm)
  have he : (c • (1 : Matrix (Fin n) (Fin n) K)) = C := by
    rw [← hc']
    ext i j
    by_cases h : i = j <;> simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply, h]
  refine ⟨c, ?_⟩
  have h := congrArg (fun X => B * X) he
  simpa only [C, Matrix.mul_nonsing_inv_cancel_left B _ hd, mul_smul_comm,
    mul_one] using h.symm


theorem m1_gram_symmetric_or_alternating
    (τ : Matrix (Fin n) (Fin n) K ≃ₗ[K] Matrix (Fin n) (Fin n) K)
    (hτ : Function.Involutive τ) (B : Matrix (Fin n) (Fin n) K) (hu : IsUnit B)
    (hB : ∀ X, B * τ X = X.transpose * B) (z : Fin n) :
    B.transpose = B ∨ B.transpose = -B := by
  obtain ⟨c, hc⟩ := m1_gram_transpose_scalar τ hτ B hu hB
  have hne : B ≠ 0 := by
    intro h
    have hh := congrArg (fun X : Matrix (Fin n) (Fin n) K => X z z)
      (hu.mul_left_cancel (show B * 1 = B * 0 by rw [h]; simp))
    simpa using hh
  have he : (1 : K) • B = (c * c) • B := by
    have h := congrArg Matrix.transpose hc
    rw [Matrix.transpose_transpose, Matrix.transpose_smul, hc, smul_smul] at h
    simpa only [one_smul] using h
  have hc2 : c * c = 1 := (smul_left_injective K hne he).symm
  have hsign : c = 1 ∨ c = -1 := by
    have h : (c - 1) * (c + 1) = 0 := by
      calc
        (c - 1) * (c + 1) = c * c - 1 := by ring
        _ = 0 := sub_eq_zero.mpr hc2
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hsign with rfl | rfl
  · exact Or.inl (by simpa only [one_smul] using hc)
  · exact Or.inr (by simpa only [neg_one_smul] using hc)


theorem m1_matrix_central_idempotent (A : Matrix (Fin n) (Fin n) K)
    (hz : ∀ X, X * A = A * X) (hi : A * A = A) (z : Fin n) : A = 0 ∨ A = 1 := by
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single
    (M := A) (fun i j _ => hz (Matrix.single i j 1))
  have he : c • (1 : Matrix (Fin n) (Fin n) K) = A := by
    rw [← hc]
    ext i j
    by_cases h : i = j <;> simp [Matrix.scalar_apply, Matrix.one_apply, h]
  have hcc : c * c = c := by
    have h := congrArg (fun X : Matrix (Fin n) (Fin n) K => X z z) hi
    rw [← he] at h
    simpa only [smul_mul_assoc, mul_smul_comm, one_mul, smul_smul,
      Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] using h
  rcases mul_eq_zero.mp (show c * (c - 1) = 0 by rw [mul_sub, mul_one, hcc, sub_self]) with h | h
  · left
    rw [← he, h, zero_smul]
  · right
    rw [← he, sub_eq_zero.mp h, one_smul]


theorem m1_reversal_central {A : Type*} [Ring A] [Algebra K A]
    (τ : A ≃ₗ[K] A) (hmul : ∀ X Y, τ (X * Y) = τ Y * τ X)
    (a : A) (ha : ∀ X, X * a = a * X) (X : A) : X * τ a = τ a * X := by
  have h := congrArg τ (ha (τ.symm X))
  simpa only [hmul, τ.apply_symm_apply] using h.symm

end HodgeLean.Foundations.Program
