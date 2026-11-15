import HodgeLean.Foundations.Program.WeilTorusFamilyDefs
import HodgeLean.Foundations.Program.RelativeTorusAlg
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # B6-0a proof obligations -/

noncomputable section
open scoped TensorProduct Matrix ComplexOrder
open HodgeLean.Papers HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program

theorem b60_posDef_one_sub_swap {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℂ) :
    (1 - Bᴴ * B).PosDef ↔ (1 - B * Bᴴ).PosDef := by
  letI : Invertible (1 : Matrix n n ℂ) := invertibleOne
  let K : Matrix (n ⊕ n) (n ⊕ n) ℂ := Matrix.fromBlocks 1 B Bᴴ 1
  have h₁ : K.PosDef ↔ (1 - Bᴴ * B).PosDef := by
    rw [Matrix.posDef_iff_posSemidef_and_mulVec_injective]
    rw [Matrix.PosDef.fromBlocks₁₁ B 1 Matrix.PosDef.one]
    rw [Matrix.mulVec_injective_iff_isUnit]
    rw [Matrix.isUnit_fromBlocks_iff_of_invertible₁₁]
    rw [Matrix.posDef_iff_posSemidef_and_mulVec_injective]
    simp [Matrix.mulVec_injective_iff_isUnit]
  have h₂ : K.PosDef ↔ (1 - B * Bᴴ).PosDef := by
    rw [Matrix.posDef_iff_posSemidef_and_mulVec_injective]
    rw [Matrix.PosDef.fromBlocks₂₂ 1 B Matrix.PosDef.one]
    rw [Matrix.mulVec_injective_iff_isUnit]
    rw [Matrix.isUnit_fromBlocks_iff_of_invertible₂₂]
    rw [Matrix.posDef_iff_posSemidef_and_mulVec_injective]
    simp [Matrix.mulVec_injective_iff_isUnit]
  exact h₁.symm.trans h₂

theorem b60_omega_square_aux  :
    b60_omega.comp b60_omega = (-3 : ℤ) • LinearMap.id := by
  ext x p
  rcases p with ⟨i, j⟩
  fin_cases j <;> simp [b60_omega, LinearMap.comp_apply]

theorem b60_trace_pairing_aux (x y : b60_Lattice) :
    (b60_E x y : ℚ) = QuadraticAlgebra.trace
      (b60_H (b60_rat x) (b60_rat y) / (2 * QuadraticAlgebra.omega)) := by
  have hinv : ((2 * QuadraticAlgebra.omega)⁻¹ : QuadraticAlgebra ℚ (-3) 0) =
      ⟨0, -1 / 6⟩ := by
    ext <;> norm_num [QuadraticAlgebra.inv_def, QuadraticAlgebra.norm,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  rw [div_eq_mul_inv, hinv]
  simp [b60_E, b60_H, diagForm_apply, b60_rat, QuadraticAlgebra.trace_def,
    Finset.sum_mul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  fin_cases i <;> norm_num [b60_diag] <;> ring

theorem b60_eigen_coord (s : ℂ) (i j : Fin 6) (k : Fin 2) :
    b60_basis.repr (b60_eigen s i) (j, k) =
      (if i = 5 then (Real.sqrt 2 : ℂ)⁻¹ else 1) *
        (if i = j then if k = 0 then 1 else s / (Complex.I * (Real.sqrt 3 : ℂ)) else 0) := by
  fin_cases k <;> split_ifs <;> simp_all [b60_eigen]

theorem b60_omegaC_basis_zero (i : Fin 6) :
    b60_omegaC (b60_basis (i, 0)) = b60_basis (i, 1) := by
  simp only [b60_basis, Module.Basis.baseChange_apply]
  change (1 : ℂ) ⊗ₜ[ℤ] b60_omega (Pi.basisFun ℤ (Fin 6 × Fin 2) (i, 0)) = _
  rw [show b60_omega (Pi.basisFun ℤ (Fin 6 × Fin 2) (i, 0)) =
      Pi.basisFun ℤ (Fin 6 × Fin 2) (i, 1) by
    ext p
    rcases p with ⟨j, k⟩
    fin_cases k <;> simp [b60_omega, Pi.basisFun_apply] <;>
      simp only [Pi.single_apply] <;> split_ifs <;> simp_all]

theorem b60_omegaC_basis_one (i : Fin 6) :
    b60_omegaC (b60_basis (i, 1)) = -3 • b60_basis (i, 0) := by
  simp only [b60_basis, Module.Basis.baseChange_apply]
  change (1 : ℂ) ⊗ₜ[ℤ] b60_omega (Pi.basisFun ℤ (Fin 6 × Fin 2) (i, 1)) = _
  rw [show b60_omega (Pi.basisFun ℤ (Fin 6 × Fin 2) (i, 1)) =
      (-3 : ℤ) • Pi.basisFun ℤ (Fin 6 × Fin 2) (i, 0) by
    ext p
    rcases p with ⟨j, k⟩
    fin_cases k <;> simp [b60_omega, Pi.basisFun_apply] <;>
      simp only [Pi.single_apply] <;> split_ifs <;> simp_all]
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']

theorem b60_pairing_basis (i j : Fin 6) (a b : Fin 2) :
    b60_E.baseChange ℂ (b60_basis (i, a)) (b60_basis (j, b)) =
      if i = j then if a = 0 ∧ b = 1 then b60_diag i else
        if a = 1 ∧ b = 0 then -b60_diag i else 0 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [b60_basis, b60_E, Pi.basisFun_apply] <;>
    simp only [Pi.single_apply] <;> split_ifs <;> simp_all <;> aesop

theorem b60_conj_basis (p : Fin 6 × Fin 2) :
    b2_conj b60_Lattice (b60_basis p) = b60_basis p := by
  simp only [b60_basis, Module.Basis.baseChange_apply]
  exact b2a_conj_incl _

theorem b60_conj_eigen (s : ℂ) (hs : s = 1 ∨ s = -1) (i : Fin 6) :
    b2_conj b60_Lattice (b60_eigen s i) = b60_eigen (-s) i := by
  simp only [b60_eigen, b2a_conj_smul, map_add, b60_conj_basis]
  have hr : starRingEnd ℂ (Real.sqrt 3 : ℂ) = Real.sqrt 3 := by simp
  have hsqrt : (Real.sqrt 3 : ℂ) ≠ 0 := by positivity
  rcases hs with rfl | rfl <;> split_ifs <;>
    simp [map_inv₀, map_div₀, hr, Complex.star_def] <;>
    congr 1 <;> field_simp [hsqrt, Complex.I_ne_zero] <;>
    simp [Complex.I_sq]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 2000 in
theorem b60_pairing_eigen (s t : ℂ) (i j : Fin 6) :
    b60_E.baseChange ℂ (b60_eigen s i) (b60_eigen t j) =
      if i = j then
        (if i = 5 then (Real.sqrt 2 : ℂ)⁻¹ else 1) ^ 2 * b60_diag i *
          ((t - s) / (Complex.I * (Real.sqrt 3 : ℂ)))
      else 0 := by
  simp only [b60_eigen, map_smul, LinearMap.smul_apply, map_add, smul_eq_mul]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [b60_pairing_basis i j 0 0, b60_pairing_basis i j 1 0,
    b60_pairing_basis i j 0 1, b60_pairing_basis i j 1 1]
  by_cases h : i = j
  · subst j
    simp only
    split_ifs <;> norm_num at * <;> ring
  · simp only [if_neg h]
    split_ifs <;> simp_all

set_option maxHeartbeats 400000 in
theorem b60_omegaC_eigen (s : ℂ) (hs : s = 1 ∨ s = -1) (i : Fin 6) :
    b60_omegaC (b60_eigen s i) =
      (s * Complex.I * (Real.sqrt 3 : ℂ)) • b60_eigen s i := by
  have hbasis : b60_omegaC (b60_basis (i, 1)) =
      (-3 : ℂ) • b60_basis (i, 0) := by
    rw [b60_omegaC_basis_one]
    module
  simp only [b60_eigen, map_smul, map_add, b60_omegaC_basis_zero, hbasis]
  have hr : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3))
  have hsqrt : (Real.sqrt 3 : ℂ) ≠ 0 := by positivity
  have h0 : s / (Complex.I * (Real.sqrt 3 : ℂ)) * (-3) =
      s * Complex.I * (Real.sqrt 3 : ℂ) := by
    field_simp [hsqrt]
    rw [hr, Complex.I_sq]
    ring
  split_ifs <;> simp only [smul_add, smul_smul] <;> rw [h0] <;>
    rcases hs with rfl | rfl <;> field_simp [hsqrt] <;> module

set_option maxHeartbeats 400000 in
theorem b60_frame_independent_aux (z : Fin 9 → ℂ) :
    LinearIndependent ℂ (b60_frame z) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg p
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at hg
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hg
  rcases p with ⟨a, i⟩
  let k : Fin 6 := if a = 0 then Fin.castAdd 3 i else Fin.natAdd 3 i
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by positivity
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by positivity
  have hI : (Complex.I * (Real.sqrt 3 : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero hs
  fin_cases a
  · fin_cases i
    all_goals
      have h0 := congrArg (fun v => b60_basis.repr v (k, 0)) hg
      have h1 := congrArg (fun v => b60_basis.repr v (k, 1)) hg
      simp [k, b60_frame, Fin.sum_univ_succ, b60_eigen_coord] at h0 h1
      field_simp [hI, hs2] at h0 h1
      simp [Complex.I_sq] at h1
      norm_num at ⊢
      linear_combination (h0 - h1) / 2
  · fin_cases i
    all_goals
      have h0 := congrArg (fun v => b60_basis.repr v (k, 0)) hg
      have h1 := congrArg (fun v => b60_basis.repr v (k, 1)) hg
      simp [k, b60_frame, Fin.sum_univ_succ, b60_eigen_coord] at h0 h1
      field_simp [hI, hs2] at h0 h1
      simp [Complex.I_sq] at h1
      norm_num at ⊢
      linear_combination (h0 + h1) / 2

set_option maxHeartbeats 400000 in
theorem b60_omegaC_frame (z : Fin 9 → ℂ) (p : Fin 2 × Fin 3) :
    b60_omegaC (b60_frame z p) =
      (if (p.1 : Fin 2) = 0 then -Complex.I * (Real.sqrt 3 : ℂ)
        else Complex.I * (Real.sqrt 3 : ℂ)) • b60_frame z p := by
  rcases p with ⟨a, i⟩
  fin_cases a
  · simp [b60_frame, b60_omegaC_eigen]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    module
  · simp [b60_frame, b60_omegaC_eigen]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    module

set_option maxHeartbeats 400000 in
theorem b60_pairing_frame (z : Fin 9 → ℂ) (p q : Fin 2 × Fin 3) :
    b60_E.baseChange ℂ (b60_frame z p) (b60_frame z q) = 0 := by
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by positivity
  have hsq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
  have hnorm : ((Real.sqrt 2 : ℂ) ^ 2)⁻¹ = 1 / 2 := by rw [hsq]; norm_num
  rcases p with ⟨a, i⟩
  rcases q with ⟨b, j⟩
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [b60_frame, b60_pairing_eigen, Finset.sum_apply,
      Finset.sum_mul, Finset.mul_sum, Fin.sum_univ_succ, b60_diag] <;>
    rw [hnorm] <;> ring

set_option maxHeartbeats 400000 in
theorem b60_riemann_frame_gram (z : Fin 9 → ℂ) (p q : Fin 2 × Fin 3) :
    Complex.I * b60_E.baseChange ℂ (b60_frame z p)
      (b2_conj b60_Lattice (b60_frame z q)) =
      (2 / (Real.sqrt 3 : ℂ)) *
        if p.1 = q.1 then
          if p.1 = 0 then (1 - (g32m_toMat z)ᴴ * g32m_toMat z) q.2 p.2
          else (1 - g32m_toMat z * (g32m_toMat z)ᴴ) p.2 q.2
        else 0 := by
  have hsq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
  have hnorm : ((Real.sqrt 2 : ℂ) ^ 2)⁻¹ = 1 / 2 := by rw [hsq]; norm_num
  have hs3 : (Real.sqrt 3 : ℂ) ≠ 0 := by positivity
  rcases p with ⟨a, i⟩
  rcases q with ⟨b, j⟩
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [b60_frame, b2a_conj_smul, b60_conj_eigen, b60_pairing_eigen,
      Fin.sum_univ_succ, b60_diag, Matrix.mul_apply, Matrix.conjTranspose_apply] <;>
    (try rw [hnorm]) <;> field_simp [hs3, Complex.I_ne_zero] <;> ring

set_option maxHeartbeats 400000 in
theorem b60_riemann_quadratic (z : Fin 9 → ℂ) (g : Fin 2 × Fin 3 → ℂ) :
    Complex.I * b60_E.baseChange ℂ (∑ p, g p • b60_frame z p)
      (b2_conj b60_Lattice (∑ p, g p • b60_frame z p)) =
      (2 / (Real.sqrt 3 : ℂ)) *
        (star (fun i => g (0, i)) ⬝ᵥ
            ((1 - (g32m_toMat z)ᴴ * g32m_toMat z) *ᵥ fun i => g (0, i)) +
          star (fun i => g (1, i)) ⬝ᵥ
            ((1 - g32m_toMat z * (g32m_toMat z)ᴴ)ᵀ *ᵥ fun i => g (1, i))) := by
  have hpair (p q : Fin 2 × Fin 3) :
      b60_E.baseChange ℂ (b60_frame z p) (b2_conj b60_Lattice (b60_frame z q)) =
        -Complex.I * ((2 / (Real.sqrt 3 : ℂ)) *
          if p.1 = q.1 then
            if p.1 = 0 then (1 - (g32m_toMat z)ᴴ * g32m_toMat z) q.2 p.2
            else (1 - g32m_toMat z * (g32m_toMat z)ᴴ) p.2 q.2
          else 0) := by
    have hunit : -Complex.I * Complex.I = 1 := by
      calc
        -Complex.I * Complex.I = -(Complex.I * Complex.I) := by ring
        _ = 1 := by rw [Complex.I_mul_I]; norm_num
    calc
      _ = -Complex.I * (Complex.I * b60_E.baseChange ℂ (b60_frame z p)
          (b2_conj b60_Lattice (b60_frame z q))) := by
            rw [← mul_assoc, hunit, one_mul]
      _ = _ := congrArg (fun w : ℂ => -Complex.I * w)
        (b60_riemann_frame_gram z p q)
  simp only [map_sum, b2a_conj_smul, map_smul, LinearMap.smul_apply, smul_eq_mul,
    Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]
  simp_rw [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  simp_rw [hpair, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, Fin.sum_univ_succ, dotProduct, Matrix.mulVec,
    Matrix.mul_apply, Matrix.transpose_apply, Complex.I_sq]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem b60_transpose_quadratic (z : Fin 9 → ℂ) (b : Fin 3 → ℂ) :
    star b ⬝ᵥ ((1 - g32m_toMat z * (g32m_toMat z)ᴴ)ᵀ *ᵥ b) =
      star (star b) ⬝ᵥ
        ((1 - g32m_toMat z * (g32m_toMat z)ᴴ) *ᵥ star b) := by
  simp [dotProduct, Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.transpose_apply, Matrix.conjTranspose_apply]
  ring

set_option maxHeartbeats 400000 in
theorem b60_riemann_positive_iff (z : Fin 9 → ℂ) :
    (∀ x ∈ b60_F z, x ≠ 0 →
      0 < (Complex.I * b60_E.baseChange ℂ x (b2_conj b60_Lattice x)).re) ↔
      (1 - (g32m_toMat z)ᴴ * g32m_toMat z).PosDef := by
  let A := 1 - (g32m_toMat z)ᴴ * g32m_toMat z
  let C := 1 - g32m_toMat z * (g32m_toMat z)ᴴ
  constructor
  · intro hp
    have hAh : A.IsHermitian := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [A, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;> ring
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hAh
    intro a ha
    let g : Fin 2 × Fin 3 → ℂ := fun p => if p.1 = 0 then a p.2 else 0
    let x := ∑ p, g p • b60_frame z p
    have hg : g ≠ 0 := by
      intro hg
      apply ha
      funext i
      have h := congrFun hg (0, i)
      simpa [g] using h
    have hx0 : x ≠ 0 := by
      intro hx
      have hli := Fintype.linearIndependent_iff.mp (b60_frame_independent_aux z) g hx
      exact hg (funext hli)
    have hx : x ∈ b60_F z := by
      rw [b60_F]
      exact Submodule.sum_mem _ fun p _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
    have h := hp x hx hx0
    rw [b60_riemann_quadratic] at h
    have hre : 0 < (star a ⬝ᵥ (A *ᵥ a)).re := by
      simpa [g, A, dotProduct, Matrix.mulVec] using h
    apply Complex.pos_iff.mpr
    refine ⟨hre, ?_⟩
    have hs := hAh.star_dotProduct_mulVec_comm a a
    have him := congrArg Complex.im hs
    simp only [map_star, Complex.star_def, Complex.conj_im] at him
    linarith
  · intro hA x hx hx0
    rw [b60_F] at hx
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
    have hg : g ≠ 0 := by
      intro hg
      apply hx0
      simp [hg]
    let a : Fin 3 → ℂ := fun i => g (0, i)
    let b : Fin 3 → ℂ := fun i => g (1, i)
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push_neg at h
      apply hg
      ext p
      rcases p with ⟨k, i⟩
      fin_cases k
      · exact congrFun h.1 i
      · exact congrFun h.2 i
    have hC : C.PosDef := (b60_posDef_one_sub_swap (g32m_toMat z)).mp hA
    have hqa : 0 ≤ star a ⬝ᵥ (A *ᵥ a) := hA.posSemidef.dotProduct_mulVec_nonneg a
    have hqb : 0 ≤ star b ⬝ᵥ (Cᵀ *ᵥ b) := by
      rw [b60_transpose_quadratic]
      exact hC.posSemidef.dotProduct_mulVec_nonneg (star b)
    have hsum : 0 < (star a ⬝ᵥ (A *ᵥ a)) + (star b ⬝ᵥ (Cᵀ *ᵥ b)) := by
      rcases hab with ha | hb
      · exact add_pos_of_pos_of_nonneg (hA.dotProduct_mulVec_pos ha) hqb
      · apply add_pos_of_nonneg_of_pos hqa
        rw [b60_transpose_quadratic]
        exact hC.dotProduct_mulVec_pos (by simpa using star_injective.ne hb)
    rw [b60_riemann_quadratic]
    change 0 < ((2 / (Real.sqrt 3 : ℂ)) *
      ((star a ⬝ᵥ (A *ᵥ a)) + (star b ⬝ᵥ (Cᵀ *ᵥ b)))).re
    have hs := (Complex.pos_iff.mp hsum).1
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    norm_num
    positivity

theorem b60_pairing_F (z : Fin 9 → ℂ) (x : ℂ ⊗[ℤ] b60_Lattice) (hx : x ∈ b60_F z)
    (y : ℂ ⊗[ℤ] b60_Lattice) (hy : y ∈ b60_F z) :
    b60_E.baseChange ℂ x y = 0 := by
  rw [b60_F] at hx hy
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hy
  simp [b60_pairing_frame]

theorem b60_weight_one_of_riemann (z : Fin 9 → ℂ)
    (hR : b2_IsRiemannForm b60_Lattice (b60_F z) b60_E) :
    b2_IsWeightOne b60_Lattice (b60_F z) := by
  have hdis : b60_F z ⊓ b2_conjSubmodule b60_Lattice (b60_F z) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    by_contra hx0
    have hc : b2_conj b60_Lattice x ∈ b60_F z :=
      b2a_conj_mem_of_mem_conjSubmodule hx.2
    have hi := hR.isotropic x hx.1 (b2_conj b60_Lattice x) hc
    have hp := hR.positive x hx.1 hx0
    rw [hi] at hp
    norm_num at hp
  refine ⟨?_, ?_⟩
  · exact disjoint_iff_inf_le.mpr (by rw [hdis])
  · rw [codisjoint_iff]
    apply Submodule.eq_top_of_finrank_eq
    have hF : Module.finrank ℂ ↥(b60_F z) = 6 := by
      rw [b60_F, finrank_span_eq_card (b60_frame_independent_aux z)]
      decide
    have hcF : Module.finrank ℂ ↥(b2_conjSubmodule b60_Lattice (b60_F z)) = 6 := by
      rw [b2a_finrank_conjSubmodule, hF]
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (b60_F z) (b2_conjSubmodule b60_Lattice (b60_F z))
    rw [hdis, hF, hcF] at h
    simp at h
    calc
      Module.finrank ℂ ↥(b60_F z ⊔ b2_conjSubmodule b60_Lattice (b60_F z)) = 12 := h
      _ = Module.finrank ℂ (ℂ ⊗[ℤ] b60_Lattice) := by
        rw [Module.finrank_eq_card_basis b60_basis]
        decide

theorem b60_weight_one_aux (τ : g32m_Domain) :
    b2_IsWeightOne b60_Lattice (b60_F τ) := by
  apply b60_weight_one_of_riemann
  have hpos : (1 - (g32m_toMat (τ : Fin 9 → ℂ))ᴴ *
      g32m_toMat (τ : Fin 9 → ℂ)).PosDef := by
    have hτ : (τ : Fin 9 → ℂ) ∈ (g32m_Domain : Set (Fin 9 → ℂ)) := τ.property
    rw [g32m_domain_coe] at hτ
    exact hτ
  refine ⟨?_, b60_pairing_F τ, (b60_riemann_positive_iff τ).mpr hpos⟩
  intro x
  simp [b60_E]
  apply Finset.sum_eq_zero
  intro i hi
  ring

theorem b60_riemann_iff_aux (z : Fin 9 → ℂ) :
    b2_IsRiemannForm b60_Lattice (b60_F z) b60_E ↔ z ∈ g32m_Domain := by
  constructor
  · intro hR
    change z ∈ (g32m_Domain : Set (Fin 9 → ℂ))
    rw [g32m_domain_coe]
    exact (b60_riemann_positive_iff z).mp hR.positive
  · intro hz
    have hpos : (1 - (g32m_toMat z)ᴴ * g32m_toMat z).PosDef := by
      change z ∈ (g32m_Domain : Set (Fin 9 → ℂ)) at hz
      rw [g32m_domain_coe] at hz
      exact hz
    refine ⟨?_, b60_pairing_F z, (b60_riemann_positive_iff z).mpr hpos⟩
    intro x
    simp [b60_E]
    apply Finset.sum_eq_zero
    intro i hi
    ring

theorem b60_omega_preserves_aux (z : Fin 9 → ℂ) :
    Submodule.map b60_omegaC (b60_F z) ≤ b60_F z := by
  rw [b60_F, Submodule.map_span]
  apply Submodule.span_le.2
  rintro y ⟨x, ⟨p, rfl⟩, rfl⟩
  rw [b60_omegaC_frame]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

set_option maxHeartbeats 400000 in
theorem b60_weil_dimensions_aux (z : Fin 9 → ℂ) :
    Module.finrank ℂ ↥(b60_F z ⊓ Module.End.eigenspace b60_omegaC
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3 ∧
    Module.finrank ℂ ↥(b60_F z ⊓ Module.End.eigenspace b60_omegaC
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3 := by
  let P := b60_F z ⊓ Module.End.eigenspace b60_omegaC
    (Complex.I * (Real.sqrt 3 : ℂ))
  let N := b60_F z ⊓ Module.End.eigenspace b60_omegaC
    (-Complex.I * (Real.sqrt 3 : ℂ))
  let fp : Fin 3 → ℂ ⊗[ℤ] b60_Lattice := fun i => b60_frame z (1, i)
  let fn : Fin 3 → ℂ ⊗[ℤ] b60_Lattice := fun i => b60_frame z (0, i)
  have hpLI : LinearIndependent ℂ fp :=
    (b60_frame_independent_aux z).comp (fun i => (1, i)) (by intro a b h; simpa using h)
  have hnLI : LinearIndependent ℂ fn :=
    (b60_frame_independent_aux z).comp (fun i => (0, i)) (by intro a b h; simpa using h)
  have hp : Submodule.span ℂ (Set.range fp) ≤ P := by
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    refine ⟨Submodule.subset_span ⟨(1, i), rfl⟩, ?_⟩
    apply Module.End.mem_eigenspace_iff.mpr
    dsimp only [fp]
    rw [b60_omegaC_frame]
    simp
  have hn : Submodule.span ℂ (Set.range fn) ≤ N := by
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    refine ⟨Submodule.subset_span ⟨(0, i), rfl⟩, ?_⟩
    apply Module.End.mem_eigenspace_iff.mpr
    dsimp only [fn]
    rw [b60_omegaC_frame]
    simp
  have hsup : P ⊔ N = b60_F z := by
    apply le_antisymm
    · exact sup_le inf_le_left inf_le_left
    · rw [b60_F, Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      rcases p with ⟨a, i⟩
      fin_cases a
      · exact Submodule.mem_sup_right (hn (Submodule.subset_span ⟨i, rfl⟩))
      · exact Submodule.mem_sup_left (hp (Submodule.subset_span ⟨i, rfl⟩))
  have hinf : P ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hpos : b60_omegaC x = (Complex.I * (Real.sqrt 3 : ℂ)) • x :=
      Module.End.mem_eigenspace_iff.mp hx.1.2
    have hneg : b60_omegaC x = (-Complex.I * (Real.sqrt 3 : ℂ)) • x :=
      Module.End.mem_eigenspace_iff.mp hx.2.2
    have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by positivity
    have heq := hpos.symm.trans hneg
    have hcoef : (Complex.I * (Real.sqrt 3 : ℂ) * 2) • x = 0 := by
      have h := sub_eq_zero.mpr heq
      rw [← sub_smul] at h
      convert h using 1 <;> ring
    exact (smul_eq_zero.mp hcoef).resolve_left
      (mul_ne_zero (mul_ne_zero Complex.I_ne_zero hs) (by norm_num))
  have hF : Module.finrank ℂ ↥(b60_F z) = 6 := by
    rw [b60_F, finrank_span_eq_card (b60_frame_independent_aux z)]
    decide
  have hsum : Module.finrank ℂ ↥P + Module.finrank ℂ ↥N = 6 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P N
    rw [hsup, hinf, hF] at h
    simp at h
    omega
  have hp3 : 3 ≤ Module.finrank ℂ ↥P := by
    calc
      3 = Module.finrank ℂ ↥(Submodule.span ℂ (Set.range fp)) := by
        rw [finrank_span_eq_card hpLI]
        decide
      _ ≤ Module.finrank ℂ ↥P := Submodule.finrank_mono hp
  have hn3 : 3 ≤ Module.finrank ℂ ↥N := by
    calc
      3 = Module.finrank ℂ ↥(Submodule.span ℂ (Set.range fn)) := by
        rw [finrank_span_eq_card hnLI]
        decide
      _ ≤ Module.finrank ℂ ↥N := Submodule.finrank_mono hn
  change Module.finrank ℂ ↥P = 3 ∧ Module.finrank ℂ ↥N = 3
  omega

theorem b60_frame_holomorphic_aux (p : Fin 2 × Fin 3) (q : Fin 6 × Fin 2) :
    Differentiable ℂ (fun z : Fin 9 → ℂ => b60_frameCoord z p q) := by
  unfold b60_frameCoord b60_frame
  split
  all_goals
    simp only [map_add, map_sum, map_smul, Finsupp.add_apply]
    simp [Fin.sum_univ_succ, g32m_toMat]
    fun_prop (disch := aesop)

end HodgeLean.Foundations.Program
