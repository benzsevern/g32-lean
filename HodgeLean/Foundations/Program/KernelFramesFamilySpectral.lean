import HodgeLean.Foundations.Program.KernelFramesFamilyDefs

/-! # B6-5 stage 5d, family part: Lagrange spectral projectors and normalized eigenbases

For a matrix annihilated by the product of the distinct linear factors over an exponent list,
the Lagrange projectors of `b65q_projector` are idempotent, orthogonal, sum to one and project
onto eigenspaces. Under invertibility of the comparison matrices, `b65q_eigenbasis` is an
invertible eigenbasis with the constant exponents, normalized against the initial eigenbasis;
at the initial residue it is the initial eigenbasis.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Matrix Polynomial
namespace HodgeLean.Foundations.Program

/-- The Lagrange polynomial of `b65q_projector`. -/
def b65q_lag (lam : Fin 4 → ℂ) (μ : ℂ) : ℂ[X] :=
  ∏ ν ∈ (Finset.univ.image lam).erase μ, (C (μ - ν)⁻¹ * (X - C ν))

theorem b65q_projector_eq (A : Matrix (Fin 4) (Fin 4) ℂ) (lam : Fin 4 → ℂ) (μ : ℂ) :
    b65q_projector A lam μ = aeval A (b65q_lag lam μ) := rfl

theorem b65q_lag_eval (lam : Fin 4 → ℂ) {μ ν : ℂ} (hν : ν ∈ Finset.univ.image lam) :
    (b65q_lag lam μ).eval ν = if ν = μ then 1 else 0 := by
  rw [b65q_lag, eval_prod]
  split_ifs with h
  · subst h
    refine Finset.prod_eq_one fun ν' hν' ↦ ?_
    have : ν - ν' ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hν').symm
    simp [this]
  · exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨h, hν⟩) (by simp)

theorem b65q_aeval_mul_basis (A P : Matrix (Fin 4) (Fin 4) ℂ) (lam : Fin 4 → ℂ)
    (hAP : A * P = P * diagonal lam) (f : ℂ[X]) :
    aeval A f * P = P * diagonal (fun i ↦ f.eval (lam i)) := by
  induction f using Polynomial.induction_on with
  | C a =>
    rw [aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    ext i j; simp [Matrix.mul_apply, diagonal, mul_comm]
  | add f g hf hg =>
    rw [map_add, add_mul, hf, hg, ← mul_add, diagonal_add]
    simp
  | monomial k a h =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, mul_assoc, hAP, ← mul_assoc, h, mul_assoc,
      diagonal_mul_diagonal]
    simp [mul_assoc]

theorem b65q_aeval_eq_zero (A P : Matrix (Fin 4) (Fin 4) ℂ) (lam : Fin 4 → ℂ) (hP : IsUnit P)
    (hAP : A * P = P * diagonal lam) (f : ℂ[X]) (hf : ∀ i, f.eval (lam i) = 0) :
    aeval A f = 0 := by
  have h := b65q_aeval_mul_basis A P lam hAP f
  rw [show diagonal (fun i ↦ f.eval (lam i)) = 0 by ext i j; simp [diagonal, hf], mul_zero] at h
  have : aeval A f * P * P⁻¹ = 0 := by rw [h, zero_mul]
  rwa [mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det P).mp hP), mul_one] at this

/-- The product of the distinct linear factors over the values of `lam`. -/
def b65q_minpoly (lam : Fin 4 → ℂ) : ℂ[X] := ∏ ν ∈ Finset.univ.image lam, (X - C ν)

theorem b65q_aeval_vanish (A : Matrix (Fin 4) (Fin 4) ℂ) (lam : Fin 4 → ℂ)
    (hm : aeval A (b65q_minpoly lam) = 0) (g : ℂ[X])
    (hg : ∀ ν ∈ Finset.univ.image lam, g.eval ν = 0) : aeval A g = 0 := by
  have hdvd : b65q_minpoly lam ∣ g := by
    apply Finset.prod_dvd_of_coprime
    · intro a _ b _ hab
      exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit
    · intro ν hν
      exact dvd_iff_isRoot.mpr (hg ν hν)
  obtain ⟨q, hq⟩ := hdvd
  rw [hq, map_mul, hm, zero_mul]

section
variable (A : Matrix (Fin 4) (Fin 4) ℂ) (lam : Fin 4 → ℂ)

theorem b65q_proj_idem (hm : aeval A (b65q_minpoly lam) = 0) {μ : ℂ} (hμ : μ ∈ Finset.univ.image lam) :
    b65q_projector A lam μ * b65q_projector A lam μ = b65q_projector A lam μ := by
  rw [b65q_projector_eq, ← map_mul, ← sub_eq_zero, ← map_sub]
  apply b65q_aeval_vanish A lam hm
  intro ν hν
  rw [eval_sub, eval_mul, b65q_lag_eval lam hν]
  split_ifs <;> simp

theorem b65q_proj_eig (hm : aeval A (b65q_minpoly lam) = 0) {μ : ℂ} (hμ : μ ∈ Finset.univ.image lam) :
    A * b65q_projector A lam μ = μ • b65q_projector A lam μ := by
  rw [b65q_projector_eq, ← sub_eq_zero]
  have : A * aeval A (b65q_lag lam μ) - μ • aeval A (b65q_lag lam μ) =
      aeval A ((X - C μ) * b65q_lag lam μ) := by
    rw [map_mul, map_sub, aeval_X, aeval_C, sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul]
  rw [this]
  apply b65q_aeval_vanish A lam hm
  intro ν hν
  rw [eval_mul, b65q_lag_eval lam hν]
  split_ifs with h <;> simp [h]

theorem b65q_proj_orth (hm : aeval A (b65q_minpoly lam) = 0) {μ ν : ℂ} (hμ : μ ∈ Finset.univ.image lam) (hν : ν ∈ Finset.univ.image lam)
    (hne : μ ≠ ν) : b65q_projector A lam μ * b65q_projector A lam ν = 0 := by
  rw [b65q_projector_eq, b65q_projector_eq, ← map_mul]
  apply b65q_aeval_vanish A lam hm
  intro ξ hξ
  rw [eval_mul, b65q_lag_eval lam hξ, b65q_lag_eval lam hξ]
  split_ifs with h1 h2 <;> simp_all

theorem b65q_proj_sum (hm : aeval A (b65q_minpoly lam) = 0) :
    ∑ μ ∈ Finset.univ.image lam, b65q_projector A lam μ = 1 := by
  rw [← sub_eq_zero]
  simp only [b65q_projector_eq]
  rw [← map_sum, ← map_one (aeval (R := ℂ) A), ← map_sub]
  apply b65q_aeval_vanish A lam hm
  intro ξ hξ
  rw [eval_sub, eval_finset_sum, eval_one]
  simp only [b65q_lag_eval lam hξ]
  rw [Finset.sum_ite_eq]
  simp [hξ]
end

theorem b65q_minpoly_base (A₀ P₀ : Matrix (Fin 4) (Fin 4) ℂ) (lam : Fin 4 → ℂ) (hP₀ : IsUnit P₀)
    (hA₀ : A₀ * P₀ = P₀ * diagonal lam) : aeval A₀ (b65q_minpoly lam) = 0 :=
  b65q_aeval_eq_zero A₀ P₀ lam hP₀ hA₀ _ fun i ↦ by
    rw [b65q_minpoly, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_image_of_mem lam (Finset.mem_univ i)) (by simp)

theorem b65q_proj_basis (A₀ P₀ : Matrix (Fin 4) (Fin 4) ℂ) (lam : Fin 4 → ℂ)
    (hA₀ : A₀ * P₀ = P₀ * diagonal lam) (i : Fin 4) :
    b65q_projector A₀ lam (lam i) * P₀ =
      P₀ * diagonal (fun j ↦ if lam j = lam i then 1 else 0) := by
  rw [b65q_projector_eq, b65q_aeval_mul_basis A₀ P₀ lam hA₀]
  congr 2; funext j
  exact b65q_lag_eval lam (Finset.mem_image_of_mem lam (Finset.mem_univ j))

/-- The normalized eigenbasis of the initial residue is the initial eigenbasis. -/
theorem b65q_eigenbasis_base (A₀ P₀ : Matrix (Fin 4) (Fin 4) ℂ) (lam : Fin 4 → ℂ)
    (hP₀ : IsUnit P₀) (hA₀ : A₀ * P₀ = P₀ * diagonal lam) :
    b65q_eigenbasis A₀ A₀ P₀ lam = P₀ := by
  have hm := b65q_minpoly_base A₀ P₀ lam hP₀ hA₀
  ext r i
  have hidem := b65q_proj_idem A₀ lam hm (Finset.mem_image_of_mem lam (Finset.mem_univ i))
  simp only [b65q_eigenbasis, Matrix.of_apply, hidem, add_sub_cancel_left, inv_one, mul_one]
  rw [b65q_proj_basis A₀ P₀ lam hA₀ i]
  simp [Matrix.mul_diagonal]

section
variable (A A₀ P₀ : Matrix (Fin 4) (Fin 4) ℂ) (lam : Fin 4 → ℂ)

/-- The column matrix `Π(A) X⁻¹ P₀` of the normalized eigenbasis, for the eigenvalue `lam i`. -/
def b65q_colMat (i : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  b65q_projector A lam (lam i) *
    (b65q_projector A₀ lam (lam i) * b65q_projector A lam (lam i) + 1 -
      b65q_projector A₀ lam (lam i))⁻¹ * P₀

theorem b65q_eigenbasis_apply (r i : Fin 4) :
    b65q_eigenbasis A A₀ P₀ lam r i = b65q_colMat A A₀ P₀ lam i r i := rfl


theorem b65q_colMat_proj0 (hP₀ : IsUnit P₀) (hA₀ : A₀ * P₀ = P₀ * diagonal lam)
    (hX : ∀ i, IsUnit (b65q_projector A₀ lam (lam i) * b65q_projector A lam (lam i) + 1 -
      b65q_projector A₀ lam (lam i))) (i : Fin 4) :
    b65q_projector A₀ lam (lam i) * b65q_colMat A A₀ P₀ lam i =
      b65q_projector A₀ lam (lam i) * P₀ := by
  have hmem := Finset.mem_image_of_mem lam (Finset.mem_univ i)
  have h0 := b65q_proj_idem A₀ lam (b65q_minpoly_base A₀ P₀ lam hP₀ hA₀) hmem
  set Q0 := b65q_projector A₀ lam (lam i)
  set Q1 := b65q_projector A lam (lam i)
  set Xm := Q0 * Q1 + 1 - Q0
  have hXX : Xm * Xm⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp (hX i))
  have key : Xm * Xm⁻¹ * P₀ = P₀ := by rw [hXX, one_mul]
  have := congrArg (fun M ↦ Q0 * M) key
  simp only [Xm, add_mul, sub_mul, mul_add, mul_sub, one_mul, ← mul_assoc, h0] at this
  simp only [b65q_colMat]
  rw [← mul_assoc, ← mul_assoc]
  calc Q0 * Q1 * Xm⁻¹ * P₀ = Q0 * Q1 * Xm⁻¹ * P₀ + Q0 * Xm⁻¹ * P₀ - Q0 * Xm⁻¹ * P₀ := by abel
    _ = Q0 * P₀ := this

theorem b65q_eigenbasis_eig (hm : aeval A (b65q_minpoly lam) = 0) :
    A * b65q_eigenbasis A A₀ P₀ lam = b65q_eigenbasis A A₀ P₀ lam * diagonal lam := by
  ext r i
  have hmem := Finset.mem_image_of_mem lam (Finset.mem_univ i)
  have he := b65q_proj_eig A lam hm hmem
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  simp only [b65q_eigenbasis_apply]
  have : (A * b65q_colMat A A₀ P₀ lam i) r i = lam i * b65q_colMat A A₀ P₀ lam i r i := by
    simp only [b65q_colMat, ← mul_assoc, he]
    simp [Matrix.smul_mul]
  rw [← Matrix.mul_apply, this, mul_comm]

theorem b65q_eigenbasis_norm (hP₀ : IsUnit P₀) (hA₀ : A₀ * P₀ = P₀ * diagonal lam)
    (hX : ∀ i, IsUnit (b65q_projector A₀ lam (lam i) * b65q_projector A lam (lam i) + 1 -
      b65q_projector A₀ lam (lam i))) (i j : Fin 4) (hij : lam i = lam j) :
    (P₀⁻¹ * b65q_eigenbasis A A₀ P₀ lam) i j = if i = j then 1 else 0 := by
  have hdet := (isUnit_iff_isUnit_det P₀).mp hP₀
  have hb := b65q_proj_basis A₀ P₀ lam hA₀ j
  have hc := b65q_colMat_proj0 A A₀ P₀ lam hP₀ hA₀ hX j
  have hl : P₀⁻¹ * b65q_projector A₀ lam (lam j) =
      diagonal (fun l ↦ if lam l = lam j then 1 else 0) * P₀⁻¹ := by
    have := congrArg (fun M ↦ P₀⁻¹ * M * P₀⁻¹) hb
    simp only [← mul_assoc, nonsing_inv_mul _ hdet, one_mul] at this
    rw [mul_assoc, mul_nonsing_inv _ hdet, mul_one] at this
    exact this
  have h1 : (P₀⁻¹ * b65q_eigenbasis A A₀ P₀ lam) i j = (P₀⁻¹ * b65q_colMat A A₀ P₀ lam j) i j := by
    simp [Matrix.mul_apply, b65q_eigenbasis_apply]
  have h2 : (P₀⁻¹ * (b65q_projector A₀ lam (lam j) * b65q_colMat A A₀ P₀ lam j)) i j =
      (P₀⁻¹ * b65q_colMat A A₀ P₀ lam j) i j := by
    rw [← mul_assoc, hl, mul_assoc, diagonal_mul]
    simp [hij]
  rw [h1, ← h2, hc, ← mul_assoc, hl, mul_assoc, nonsing_inv_mul _ hdet, mul_one]
  simp [diagonal, hij, Matrix.one_apply]

theorem b65q_eigenbasis_isUnit (hm : aeval A (b65q_minpoly lam) = 0) (hP₀ : IsUnit P₀)
    (hA₀ : A₀ * P₀ = P₀ * diagonal lam)
    (hX : ∀ i, IsUnit (b65q_projector A₀ lam (lam i) * b65q_projector A lam (lam i) + 1 -
      b65q_projector A₀ lam (lam i))) :
    IsUnit (b65q_eigenbasis A A₀ P₀ lam) := by
  have hdet := (isUnit_iff_isUnit_det P₀).mp hP₀
  set P := b65q_eigenbasis A A₀ P₀ lam
  have hD : ∀ μ ∈ Finset.univ.image lam,
      b65q_projector A₀ lam μ * b65q_projector A lam μ * P =
        P₀ * diagonal (fun j ↦ if lam j = μ then 1 else 0) := by
    intro μ hμ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hμ
    ext r j
    rw [Matrix.mul_apply]
    simp only [P, b65q_eigenbasis_apply]
    by_cases hj : lam j = lam i
    · have hmemj := Finset.mem_image_of_mem lam (Finset.mem_univ j)
      have hidem := b65q_proj_idem A lam hm hmemj
      have hc := b65q_colMat_proj0 A A₀ P₀ lam hP₀ hA₀ hX j
      have hb := b65q_proj_basis A₀ P₀ lam hA₀ j
      have e1 : b65q_projector A lam (lam j) * b65q_colMat A A₀ P₀ lam j =
          b65q_colMat A A₀ P₀ lam j := by simp only [b65q_colMat, ← mul_assoc, hidem]
      have : b65q_projector A₀ lam (lam i) * b65q_projector A lam (lam i) *
          b65q_colMat A A₀ P₀ lam j = b65q_projector A₀ lam (lam j) * P₀ := by
        rw [← hj, mul_assoc, e1, hc]
      have h' := congrFun (congrFun this r) j
      rw [Matrix.mul_apply] at h'
      rw [h', hb]
      simp [Matrix.mul_apply, diagonal, hj]
    · have hmemj := Finset.mem_image_of_mem lam (Finset.mem_univ j)
      have hmemi := Finset.mem_image_of_mem lam (Finset.mem_univ i)
      have horth := b65q_proj_orth A lam hm hmemi hmemj (Ne.symm hj)
      have : b65q_projector A₀ lam (lam i) * b65q_projector A lam (lam i) *
          b65q_colMat A A₀ P₀ lam j = 0 := by
        simp only [b65q_colMat]
        rw [mul_assoc (b65q_projector A₀ lam (lam i)), ← mul_assoc (b65q_projector A lam (lam i)),
          ← mul_assoc (b65q_projector A lam (lam i)), horth]
        simp
      have h' := congrFun (congrFun this r) j
      rw [Matrix.mul_apply] at h'
      rw [h']
      simp [Matrix.mul_apply, diagonal, hj]
  have hsum : (∑ μ ∈ Finset.univ.image lam,
      P₀⁻¹ * (b65q_projector A₀ lam μ * b65q_projector A lam μ)) * P = 1 := by
    rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl fun μ hμ ↦ by rw [mul_assoc, hD μ hμ]]
    simp only [← mul_assoc, nonsing_inv_mul _ hdet, one_mul]
    ext r j
    rw [Matrix.sum_apply]
    simp [diagonal, Matrix.one_apply]
  exact (isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hsum)
end

end HodgeLean.Foundations.Program
