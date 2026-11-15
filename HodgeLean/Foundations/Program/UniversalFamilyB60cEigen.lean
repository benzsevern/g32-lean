import HodgeLean.Foundations.Program.WeilTorusFamily

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The two normalized eigenspace frames together give independent coordinates. -/
theorem b60c_eigen_independent :
    LinearIndependent ℂ (fun p : Fin 2 × Fin 6 =>
      b60_eigen (if p.1 = 0 then -1 else 1) p.2) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg p
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at hg
  rcases p with ⟨a, i⟩
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hI : (Complex.I * (Real.sqrt 3 : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero hs
  have h0 := congrArg (fun v => b60_basis.repr v (i, 0)) hg
  have h1 := congrArg (fun v => b60_basis.repr v (i, 1)) hg
  fin_cases i <;>
    simp [Fin.sum_univ_succ, b60_eigen_coord] at h0 h1 <;>
    (try field_simp [hI, hs2] at h0) <;>
    field_simp [hI, hs2] at h1 <;>
    simp [Complex.I_sq] at h1 <;>
    fin_cases a <;> norm_num at ⊢
  all_goals first | linear_combination (h0 - h1) / 2 | linear_combination (h0 + h1) / 2

#print axioms b60c_eigen_independent

/-- The normalized eigenvectors as a basis of the fixed lattice complexification. -/
def b60c_eigenBasis : Module.Basis (Fin 2 × Fin 6) ℂ (ℂ ⊗[ℤ] b60_Lattice) :=
  basisOfLinearIndependentOfCardEqFinrank b60c_eigen_independent
    (by rw [Module.finrank_eq_card_basis b60_basis]; decide)

@[simp]
theorem b60c_eigenBasis_apply (p : Fin 2 × Fin 6) :
    b60c_eigenBasis p = b60_eigen (if p.1 = 0 then -1 else 1) p.2 := by
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) p

#print axioms b60c_eigenBasis_apply

/-- The fixed quadratic action is diagonal in the normalized period basis. -/
theorem b60c_omega_eigenBasis (p : Fin 2 × Fin 6) :
    b60_omegaC (b60c_eigenBasis p) =
      ((if p.1 = 0 then -1 else 1) * Complex.I * (Real.sqrt 3 : ℂ)) •
        b60c_eigenBasis p := by
  rw [b60c_eigenBasis_apply]
  apply b60_omegaC_eigen
  split_ifs <;> simp

#print axioms b60c_omega_eigenBasis

/-- Coordinatewise diagonal action on arbitrary complexified lattice vectors. -/
theorem b60c_repr_omega (x : ℂ ⊗[ℤ] b60_Lattice) (p : Fin 2 × Fin 6) :
    b60c_eigenBasis.repr (b60_omegaC x) p =
      ((if p.1 = 0 then -1 else 1) * Complex.I * (Real.sqrt 3 : ℂ)) *
        b60c_eigenBasis.repr x p := by
  classical
  conv_lhs => rw [← b60c_eigenBasis.sum_repr x]
  simp only [map_sum, map_smul, b60c_omega_eigenBasis, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

#print axioms b60c_repr_omega

/-- An eigenvector has no coordinates in the opposite eigenspace. -/
theorem b60c_eigen_support (a b : Fin 2) (hab : a ≠ b)
    (x : ℂ ⊗[ℤ] b60_Lattice)
    (hx : b60_omegaC x =
      ((if a = 0 then -1 else 1) * Complex.I * (Real.sqrt 3 : ℂ)) • x)
    (i : Fin 6) : b60c_eigenBasis.repr x (b, i) = 0 := by
  have h := congrArg (fun v => b60c_eigenBasis.repr v (b, i)) hx
  rw [b60c_repr_omega, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  have hd : ((if b = 0 then -1 else 1) * Complex.I * (Real.sqrt 3 : ℂ)) -
      ((if a = 0 then -1 else 1) * Complex.I * (Real.sqrt 3 : ℂ)) ≠ 0 := by
    have hsign : (if b = 0 then (-1 : ℂ) else 1) -
        (if a = 0 then -1 else 1) ≠ 0 := by
      fin_cases a <;> fin_cases b <;> simp_all <;> norm_num
    convert mul_ne_zero (mul_ne_zero hsign Complex.I_ne_zero) hs using 1 <;> ring
  exact (mul_eq_zero.mp (by rw [sub_mul, h, sub_self])).resolve_left hd

#print axioms b60c_eigen_support

end HodgeLean.Foundations.Program
