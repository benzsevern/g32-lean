import HodgeLean.Foundations.Program.UniversalFamilyB60cEigen
import HodgeLean.Foundations.Program.UniversalFamilyB60cGraph

noncomputable section
open scoped TensorProduct Matrix ComplexOrder
namespace HodgeLean.Foundations.Program

/-- The eigenvector normalization changes the diagonal coefficients to signs. -/
theorem b60c_normalized_diagonal (i : Fin 6) :
    (if i = 5 then (Real.sqrt 2 : ℂ)⁻¹ else 1) ^ 2 * (b60_diag i : ℂ) =
      if i.val < 3 then 1 else -1 := by
  have hsq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  fin_cases i <;> norm_num [b60_diag, inv_pow, hsq]

#print axioms b60c_normalized_diagonal

/-- The Riemann Hermitian pairing is diagonal on each normalized eigenspace. -/
theorem b60c_eigen_hermitian_gram (s : ℂ) (hs : s = 1 ∨ s = -1)
    (i j : Fin 6) :
    Complex.I * b60_E.baseChange ℂ (b60_eigen s i)
      (b2_conj b60_Lattice (b60_eigen s j)) =
      if i = j then (-s) * (2 / (Real.sqrt 3 : ℂ)) *
        (if i.val < 3 then 1 else -1) else 0 := by
  rw [b60_conj_eigen s hs, b60_pairing_eigen]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, b60c_normalized_diagonal]
    have hr : (Real.sqrt 3 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
    field_simp [hr, Complex.I_ne_zero]
    ring
  · simp [hij]

#print axioms b60c_eigen_hermitian_gram

/-- The Riemann value of an eigenspace vector is its signed sum of squared coordinates. -/
theorem b60c_eigen_sum_hermitian (s : ℂ) (hs : s = 1 ∨ s = -1)
    (u : Fin 6 → ℂ) :
    Complex.I * b60_E.baseChange ℂ (∑ i, u i • b60_eigen s i)
      (b2_conj b60_Lattice (∑ i, u i • b60_eigen s i)) =
      (-s) * (2 / (Real.sqrt 3 : ℂ)) *
        ∑ i, (if i.val < 3 then 1 else -1) * (Complex.normSq (u i) : ℂ) := by
  have hexpand :
      Complex.I * b60_E.baseChange ℂ (∑ i, u i • b60_eigen s i)
        (b2_conj b60_Lattice (∑ i, u i • b60_eigen s i)) =
      ∑ i, ∑ j, u i * (starRingEnd ℂ) (u j) *
        (Complex.I * b60_E.baseChange ℂ (b60_eigen s i)
          (b2_conj b60_Lattice (b60_eigen s j))) := by
    simp only [map_sum, map_smul, b2a_conj_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand]
  simp_rw [b60c_eigen_hermitian_gram s hs]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.normSq_eq_conj_mul_self]
  split_ifs <;> ring

#print axioms b60c_eigen_sum_hermitian

end HodgeLean.Foundations.Program
