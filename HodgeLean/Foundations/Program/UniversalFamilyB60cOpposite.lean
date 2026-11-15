import HodgeLean.Foundations.Program.UniversalFamilyB60cChart
import HodgeLean.Foundations.Program.UniversalFamilyB60cEigenCoordinates

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Pairing with a negative eigenvector reads the corresponding positive coordinate. -/
theorem b60c_pairing_positive_coordinate (x : ℂ ⊗[ℤ] b60_Lattice)
    (hx : b60_omegaC x = (Complex.I * (Real.sqrt 3 : ℂ)) • x) (i : Fin 6) :
    Complex.I * b60_E.baseChange ℂ (b60_eigen (-1) i) x =
      (2 / (Real.sqrt 3 : ℂ)) * (if i.val < 3 then 1 else -1) *
        b60c_eigenBasis.repr x (1, i) := by
  classical
  have hrec : x = ∑ j : Fin 6,
      b60c_eigenBasis.repr x (1, j) • b60_eigen 1 j := by
    simpa using b60c_eigen_reconstruction 1 x (by simpa using hx)
  have hgram (j : Fin 6) :
      Complex.I * b60_E.baseChange ℂ (b60_eigen (-1) i) (b60_eigen 1 j) =
      if i = j then (2 / (Real.sqrt 3 : ℂ)) * (if i.val < 3 then 1 else -1) else 0 := by
    simpa [b60_conj_eigen] using b60c_eigen_hermitian_gram (-1) (Or.inr rfl) i j
  conv_lhs => rw [hrec]
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  simp_rw [mul_left_comm Complex.I, hgram, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  split_ifs <;> ring

#print axioms b60c_pairing_positive_coordinate

end HodgeLean.Foundations.Program
