import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.CompactModel

/-! # Actual Boolean carriers of complex affine polynomial models -/

noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations.ComplexTopology HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The polynomial carrier retains its actual Euclidean coordinate map when presented as a Boolean realization.
Source: real_equations_in_euclidean_coordinates; realize_realCarrierFormula.
HC no distance; AV milestone no distance. -/
theorem properCycle_polynomial_boolean_coordinates {n m : ℕ}
    (p : Fin m → MvPolynomial (Fin n) ℂ) :
    ∃ A : s2v_t11b_Formula (n+n), ∃ h : zeroSet p ≃ₜ A.realize,
      ∀ z, (h z).val = complexEuclideanCoordinates n z.val := by
  obtain ⟨a, b, hab⟩ := real_equations_in_euclidean_coordinates p
  let A := realCarrierFormula a b
  have he : zeroSet p = (complexEuclideanCoordinates n) ⁻¹' A.realize := by
    ext z
    rw [show A.realize = realPolynomialCarrier a b from realize_realCarrierFormula a b]
    exact hab z
  exact ⟨A, (complexEuclideanCoordinates n).sets he, fun _ => rfl⟩

end HodgeLean.Foundations.QuotientDuality
