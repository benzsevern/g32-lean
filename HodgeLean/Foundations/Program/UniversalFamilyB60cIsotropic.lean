import HodgeLean.Foundations.Program.UniversalFamilyB60cOpposite

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Orthogonality to a negative graph imposes the transposed graph equations. -/
theorem b60c_opposite_graph_equations (A : Matrix (Fin 3) (Fin 3) ℂ)
    (x : ℂ ⊗[ℤ] b60_Lattice)
    (hx : b60_omegaC x = (Complex.I * (Real.sqrt 3 : ℂ)) • x)
    (hiso : ∀ i : Fin 3, b60_E.baseChange ℂ
      (b60_eigen (-1) (Fin.castAdd 3 i) +
        ∑ j : Fin 3, A j i • b60_eigen (-1) (Fin.natAdd 3 j)) x = 0) :
    ∀ i : Fin 3, b60c_eigenBasis.repr x (1, Fin.castAdd 3 i) =
      ∑ j : Fin 3, A j i * b60c_eigenBasis.repr x (1, Fin.natAdd 3 j) := by
  intro i
  have h := congrArg (fun z : ℂ => Complex.I * z) (hiso i)
  simp only [map_add, map_sum, map_smul, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, mul_add,
    Finset.mul_sum, mul_zero] at h
  simp_rw [mul_left_comm Complex.I, b60c_pairing_positive_coordinate x hx] at h
  have hu (k : Fin 3) : (Fin.castAdd 3 k).val < 3 := k.is_lt
  have hl (k : Fin 3) : ¬(Fin.natAdd 3 k).val < 3 := by
    change ¬3 + k.val < 3
    omega
  simp only [hu, hl, ite_true, ite_false, mul_one, mul_neg_one] at h
  have hc : (2 / (Real.sqrt 3 : ℂ)) ≠ 0 := by
    apply div_ne_zero (by norm_num)
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp ?_).resolve_left hc
  rw [mul_sub, Finset.mul_sum]
  convert h using 1
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

#print axioms b60c_opposite_graph_equations

/-- The transposed equations reconstruct a positive eigenvector in the opposite graph frame. -/
theorem b60c_positive_graph_reconstruction (A : Matrix (Fin 3) (Fin 3) ℂ)
    (x : ℂ ⊗[ℤ] b60_Lattice)
    (hx : b60_omegaC x = (Complex.I * (Real.sqrt 3 : ℂ)) • x)
    (heq : ∀ i : Fin 3, b60c_eigenBasis.repr x (1, Fin.castAdd 3 i) =
      ∑ j : Fin 3, A j i * b60c_eigenBasis.repr x (1, Fin.natAdd 3 j)) :
    x = ∑ j : Fin 3, b60c_eigenBasis.repr x (1, Fin.natAdd 3 j) •
      (b60_eigen 1 (Fin.natAdd 3 j) +
        ∑ i : Fin 3, A j i • b60_eigen 1 (Fin.castAdd 3 i)) := by
  have hrec := b60c_eigen_reconstruction 1 x (by simpa using hx)
  rw [Fin.sum_univ_add (a := 3) (b := 3)] at hrec
  simp only [b60c_eigenBasis_apply, show (1 : Fin 2) ≠ 0 by decide, ite_false] at hrec
  conv_lhs => rw [hrec]
  simp_rw [heq]
  simp only [Finset.sum_smul, smul_add, Finset.smul_sum, smul_smul,
    Finset.sum_add_distrib]
  conv_lhs => rw [add_comm]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

#print axioms b60c_positive_graph_reconstruction

end HodgeLean.Foundations.Program
