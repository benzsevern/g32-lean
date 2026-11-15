import HodgeLean.Foundations.Program.UniversalFamilyB60cChart
import HodgeLean.Foundations.Program.UniversalFamilyB60cEigenCoordinates

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Riemann positivity on the negative eigenspace is the strict graph inequality. -/
theorem b60c_negative_eigen_positive (x : ℂ ⊗[ℤ] b60_Lattice)
    (hx : b60_omegaC x = (-Complex.I * (Real.sqrt 3 : ℂ)) • x)
    (hp : 0 < (Complex.I * b60_E.baseChange ℂ x (b2_conj b60_Lattice x)).re) :
    ∑ i : Fin 3, Complex.normSq (b60c_eigenBasis.repr x (0, Fin.natAdd 3 i)) <
      ∑ i : Fin 3, Complex.normSq (b60c_eigenBasis.repr x (0, Fin.castAdd 3 i)) := by
  let u : Fin 6 → ℂ := fun i => b60c_eigenBasis.repr x (0, i)
  have hrec : x = ∑ i, u i • b60_eigen (-1) i := by
    simpa [u] using b60c_eigen_reconstruction 0 x (by simpa using hx)
  have hsum : (∑ i : Fin 6, (if i.val < 3 then (1 : ℂ) else -1) *
      (Complex.normSq (u i) : ℂ)) =
      ((∑ i : Fin 3, Complex.normSq (u (Fin.castAdd 3 i)) -
        ∑ i : Fin 3, Complex.normSq (u (Fin.natAdd 3 i)) : ℝ) : ℂ) := by
    simp [Fin.sum_univ_succ]
    ring
  rw [hrec, b60c_eigen_sum_hermitian (-1) (Or.inr rfl), hsum] at hp
  have hr : 0 < (2 : ℝ) / Real.sqrt 3 := by positivity
  simp only [neg_neg, one_mul, ← Complex.ofReal_ofNat, ← Complex.ofReal_div,
    ← Complex.ofReal_mul, Complex.ofReal_re] at hp
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hr).mp hp)

#print axioms b60c_negative_eigen_positive

end HodgeLean.Foundations.Program
