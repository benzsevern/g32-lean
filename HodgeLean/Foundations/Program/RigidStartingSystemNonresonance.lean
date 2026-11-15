import HodgeLean.Foundations.Program.RigidStartingSystemCommutator
import HodgeLean.Foundations.Program.RigidStartingSystemSpectra

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program

theorem b65r_operator_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    b65r_operator (A+B) = b65r_operator A + b65r_operator B := by
  ext v i
  exact congrFun (Matrix.add_mulVec A B v) i

theorem b65r_operator_smul {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    b65r_operator (c • A) = c • b65r_operator A := by
  ext v i
  exact congrFun (Matrix.smul_mulVec c A v) i

theorem b65r_operator_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    b65r_operator (A*B) = b65r_operator A * b65r_operator B := by
  ext v i
  exact congrFun (Matrix.mulVec_mulVec v A B).symm i

theorem b65r_operator_one {n : ℕ} :
    b65r_operator (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext v i
  exact congrFun (Matrix.one_mulVec v) i

theorem b65r_operator_quadratic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (a b : ℂ) (hA : A*A = a • A + b • 1) :
    b65r_operator A * b65r_operator A = a • b65r_operator A + b • 1 := by
  have h := congrArg b65r_operator hA
  simpa only [b65r_operator_mul, b65r_operator_add, b65r_operator_smul,
    b65r_operator_one] using h

theorem b65r_diagonal_nonresonance {n : ℕ} (d : Fin n → ℂ) (k : ℂ)
    (hkd : ∀ i j, k - (d i - d j) ≠ 0) :
    Function.Bijective
      (fun T : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) ↦ k • T -
        (b65r_operator (diagonal d)*T-T*b65r_operator (diagonal d))) := by
  let D := b65r_operator (diagonal d)
  let L : ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) →ₗ[ℂ]
      ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :=
    k • LinearMap.id - b65r_commutator D
  have hd (v : Fin n → ℂ) (i : Fin n) : D v i = d i * v i := by
    exact Matrix.mulVec_diagonal d v i
  have hs (j : Fin n) : D (Pi.single j 1) = d j • Pi.single j 1 := by
    ext i
    rw [hd]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs with h <;> simp only [h, mul_one, mul_zero]
  have hi : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro T hT
    have hentry (j i : Fin n) : T (Pi.single j 1) i = 0 := by
      have ht := congrArg (fun U : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) ↦
        U (Pi.single j 1) i) hT
      change k * T (Pi.single j 1) i - (D (T (Pi.single j 1)) i -
        T (D (Pi.single j 1)) i) = 0 at ht
      rw [hd, hs, map_smul] at ht
      simp only [Pi.smul_apply, smul_eq_mul] at ht
      have he : (k-(d i-d j)) * T (Pi.single j 1) i = 0 := by linear_combination ht
      exact (mul_eq_zero.mp he).resolve_left (hkd i j)
    ext v i
    conv_lhs => rw [pi_eq_sum_univ' v]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hentry,
      mul_zero, Finset.sum_const_zero, _root_.zero_apply, Pi.zero_apply]
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

theorem b65r_nat_quadratic_separated (k : ℕ) (hk : 0 < k) :
    (k : ℂ) ≠ 0 ∧ (k : ℂ)^2 ≠ (1/9 : ℂ) ∧
      (k : ℂ)^2 ≠ (4/9 : ℂ) ∧ (k : ℂ)^2 ≠ (16/9 : ℂ) := by
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : k = 1 ∨ 2 ≤ k := by omega
  refine ⟨hk0, ?_, ?_, ?_⟩
  · intro h
    have hr := congrArg Complex.re h
    norm_num [pow_two, Complex.mul_re] at hr
    nlinarith
  · intro h
    have hr := congrArg Complex.re h
    norm_num [pow_two, Complex.mul_re] at hr
    nlinarith
  · rcases hk2 with rfl | h2
    · norm_num
    · intro h
      have hr := congrArg Complex.re h
      norm_num [pow_two, Complex.mul_re] at hr
      have h2r : (2 : ℝ) ≤ k := by exact_mod_cast h2
      nlinarith

theorem b65r_B0_nonresonance (k : ℕ) (hk : 0 < k) :
    Function.Bijective
      (fun T : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) ↦ (k : ℂ) • T -
        (b65r_operator b65r_B0*T-T*b65r_operator b65r_B0)) := by
  apply b65r_diagonal_nonresonance
  intro i j h
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : k = 1 ∨ 2 ≤ k := by omega
  rcases hk2 with rfl | h2
  · fin_cases i <;> fin_cases j <;> norm_num at h
  · have hr := congrArg Complex.re h
    have h2r : (2 : ℝ) ≤ k := by exact_mod_cast h2
    fin_cases i <;> fin_cases j <;>
      norm_num [Complex.sub_re] at hr <;> linarith

theorem b65r_residues_nonresonance (i : Fin 4) (k : ℕ) (hk : 0 < k) :
    Function.Bijective
      (fun T : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) ↦ (k : ℂ) • T -
        (b65r_operator (b65r_residues i)*T-T*b65r_operator (b65r_residues i))) := by
  obtain ⟨hk0, hk1, hk4, hk16⟩ := b65r_nat_quadratic_separated k hk
  fin_cases i
  · refine b65r_bijective_of_commutator_cubic _ (1/3) 0 (k : ℂ) ?_ hk0 ?_
    · apply b65r_operator_quadratic
      change b65r_B5*b65r_B5 = (1/3 : ℂ) • b65r_B5 + (0 : ℂ) • 1
      simpa only [zero_smul, add_zero] using b65r_B5_quadratic
    · convert hk1 using 1 <;> norm_num
  · refine b65r_bijective_of_commutator_cubic _ (2/3) 0 (k : ℂ) ?_ hk0 ?_
    · apply b65r_operator_quadratic
      change b65r_Bneg7*b65r_Bneg7 = (2/3 : ℂ) • b65r_Bneg7 + (0 : ℂ) • 1
      simpa only [zero_smul, add_zero] using b65r_Bneg7_quadratic
    · convert hk4 using 1 <;> norm_num
  · exact b65r_B0_nonresonance k hk
  · refine b65r_bijective_of_commutator_cubic _ 0 (4/9) (k : ℂ) ?_ hk0 ?_
    · apply b65r_operator_quadratic
      change b65r_Binf*b65r_Binf = (0 : ℂ) • b65r_Binf + (4/9 : ℂ) • 1
      simpa only [zero_smul, zero_add] using b65r_Binf_quadratic
    · convert hk16 using 1 <;> norm_num

end HodgeLean.Foundations.Program
