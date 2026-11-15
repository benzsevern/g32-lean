import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.RealCoordinates

/-! # Original polynomial values in actual Euclidean real coordinates -/

noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations.ComplexTopology
namespace HodgeLean.Foundations.QuotientDuality

/-- Every specified complex polynomial retains its real and imaginary values as real polynomials in the actual Euclidean coordinates.
Source: polynomial_real_imaginary; Homeomorph.piCongrLeft_apply_apply.
HC no distance; AV milestone no distance. -/
theorem properCycle_polynomial_real_values {n : ℕ} {ι : Type*}
    (p : ι → MvPolynomial (Fin n) ℂ) :
    ∃ a b : ι → MvPolynomial (Fin (n+n)) ℝ, ∀ z : Fin n → ℂ, ∀ j,
      MvPolynomial.eval (complexEuclideanCoordinates n z) (a j) = (MvPolynomial.eval z (p j)).re ∧
      MvPolynomial.eval (complexEuclideanCoordinates n z) (b j) = (MvPolynomial.eval z (p j)).im := by
  choose a b hab using fun j => polynomial_real_imaginary (p j)
  refine ⟨fun j => MvPolynomial.rename finSumFinEquiv (a j),
    fun j => MvPolynomial.rename finSumFinEquiv (b j), ?_⟩
  intro z j
  simp only [MvPolynomial.eval_rename]
  have he : (fun i => complexEuclideanCoordinates n z (finSumFinEquiv i)) =
      Sum.elim (fun i => (z i).re) (fun i => (z i).im) := by
    funext i
    change (Homeomorph.piCongrLeft (Y := fun _ => ℝ) finSumFinEquiv)
      (complexRealCoordinates n z) (finSumFinEquiv i) = _
    rw [Homeomorph.piCongrLeft_apply_apply]
    rfl
  simpa only [Function.comp_def, he] using hab j z

end HodgeLean.Foundations.QuotientDuality
