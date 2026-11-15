import HodgeLean.Foundations.QuotientDuality.ProperCyclePolynomialBooleanCoordinates
import HodgeLean.Foundations.QuotientDuality.ProperCyclePolynomialRealValues
import HodgeLean.Foundations.QuotientDuality.ProperCyclePolynomialProjectiveMatrix
import HodgeLean.Foundations.QuotientDuality.ProperCycleRationalCarrierGraph

/-! # Exact Boolean matrix images of actual affine polynomial carriers -/

noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations.ComplexTopology HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- A nonzero polynomial homogeneous vector on an actual complex polynomial carrier has a literal Boolean image under the original normalized projective matrix map.
Source: properCycle_rational_carrier_image; properCycle_polynomial_matrix_rational_eval.
HC no distance; AV milestone no distance. -/
theorem properCycle_polynomial_projective_image {n m : ℕ} {ι : Type} [Fintype ι]
    (p : Fin m → MvPolynomial (Fin n) ℂ) (v : ι → MvPolynomial (Fin n) ℂ)
    (hv : ∀ z : zeroSet p, (fun i => MvPolynomial.eval z.val (v i)) ≠ 0) :
    ∃ B : s2v_t11b_Formula (Fintype.card ((ι × ι) ⊕ (ι × ι))),
      B.realize = Set.range (fun z : zeroSet p => properCycle_matrix_euclidean_coordinates
        (properCycle_projective_matrix (fun i => MvPolynomial.eval z.val (v i)))) := by
  obtain ⟨A, h, hh⟩ := properCycle_polynomial_boolean_coordinates p
  obtain ⟨a, b, hab⟩ := properCycle_polynomial_real_values v
  let w (z : zeroSet p) : ι → ℂ := fun i => MvPolynomial.eval z.val (v i)
  let f (x : A.realize) := properCycle_matrix_euclidean_coordinates
    (properCycle_projective_matrix (w (h.symm x)))
  have hx (x : A.realize) : x.val = complexEuclideanCoordinates n (h.symm x).val := by
    simpa only [Homeomorph.apply_symm_apply] using hh (h.symm x)
  have hw (x : A.realize) : (fun i =>
      (⟨MvPolynomial.eval x.val (a i), MvPolynomial.eval x.val (b i)⟩ : ℂ)) = w (h.symm x) := by
    funext i
    apply Complex.ext
    · change MvPolynomial.eval x.val (a i) = _
      rw [hx]
      exact (hab (h.symm x).val i).1
    · change MvPolynomial.eval x.val (b i) = _
      rw [hx]
      exact (hab (h.symm x).val i).2
  have hq (x : A.realize) : MvPolynomial.eval x.val (properCycle_polynomial_vector_mass a b) ≠ 0 := by
    rw [properCycle_polynomial_vector_mass_eval, hw]
    exact ne_of_gt (properCycle_projective_matrix_mass_pos _ (hv (h.symm x)))
  have hf (x : A.realize) (j) : f x j =
      MvPolynomial.eval x.val (properCycle_polynomial_matrix_numerator a b j) /
        MvPolynomial.eval x.val (properCycle_polynomial_vector_mass a b) := by
    dsimp only [f]
    rw [← hw]
    exact properCycle_polynomial_matrix_rational_eval a b x.val j
  obtain ⟨B, hB⟩ := properCycle_rational_carrier_image A A
    (properCycle_polynomial_matrix_numerator a b) (properCycle_polynomial_vector_mass a b) hq f hf
  refine ⟨B, ?_⟩
  ext y
  rw [hB]
  constructor
  · rintro ⟨x, hxy, _⟩
    exact ⟨h.symm x, hxy⟩
  · rintro ⟨z, hz⟩
    refine ⟨h z, ?_, (h z).property⟩
    simpa only [f, Homeomorph.symm_apply_apply, w] using hz

end HodgeLean.Foundations.QuotientDuality
