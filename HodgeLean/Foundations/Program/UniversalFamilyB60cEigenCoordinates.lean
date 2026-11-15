import HodgeLean.Foundations.Program.UniversalFamilyB60cEigen

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Reconstruct an eigenvector from the six coordinates in its eigenspace. -/
theorem b60c_eigen_reconstruction (a : Fin 2) (x : ℂ ⊗[ℤ] b60_Lattice)
    (hx : b60_omegaC x =
      ((if a = 0 then -1 else 1) * Complex.I * (Real.sqrt 3 : ℂ)) • x) :
    x = ∑ i : Fin 6, b60c_eigenBasis.repr x (a, i) • b60c_eigenBasis (a, i) := by
  classical
  conv_lhs => rw [← b60c_eigenBasis.sum_repr x]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_single a
  · intro b _ hba
    apply Finset.sum_eq_zero
    intro i _
    rw [b60c_eigen_support a b hba.symm x hx i, zero_smul]
  · simp

#print axioms b60c_eigen_reconstruction

end HodgeLean.Foundations.Program
