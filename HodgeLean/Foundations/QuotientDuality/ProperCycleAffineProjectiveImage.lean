import HodgeLean.Foundations.QuotientDuality.ProperCyclePolynomialProjectiveImage
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Marked

/-! # Exact Boolean projective matrix images of original affine schemes -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.ComplexTopology HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- A nonzero vector of original regular functions on an affine finite type complex scheme has its literal normalized projective matrix image represented by a Boolean formula.
Source: Marked.affine_regular; properCycle_polynomial_projective_image.
HC no distance; AV milestone no distance. -/
theorem properCycle_affine_projective_matrix_image
    (X : Over (Spec ↧ℂ)) [IsAffine X.left] [LocallyOfFiniteType X.hom] {r : ℕ}
    (s : Fin r → Γ(X.left, ⊤))
    (hs : ∀ x : ComplexPoint X, (fun i => Point.evaluate ⊤ (s i) x) ≠ 0) :
    ∃ B : s2v_t11b_Formula (Fintype.card ((Fin r × Fin r) ⊕ (Fin r × Fin r))),
      B.realize = Set.range (fun x : ComplexPoint X => properCycle_matrix_euclidean_coordinates
        (properCycle_projective_matrix (fun i => Point.evaluate ⊤ (s i) x))) := by
  obtain ⟨c, hc⟩ := Marked.affine_regular X s
  have he (z : zeroSet c.equations) (j : Fin r) :
      MvPolynomial.eval z.val (c.marked j) =
        Point.evaluate ⊤ (s j) (c.coordinates.symm z).val := by
    simpa only [Homeomorph.apply_symm_apply] using c.evaluation (c.coordinates.symm z) j
  have hv (z : zeroSet c.equations) :
      (fun i => MvPolynomial.eval z.val (c.marked i)) ≠ 0 := by
    simpa only [he] using hs (c.coordinates.symm z).val
  obtain ⟨B, hB⟩ := properCycle_polynomial_projective_image c.equations c.marked hv
  refine ⟨B, hB.trans ?_⟩
  ext y
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨(c.coordinates.symm z).val, ?_⟩
    simpa only [he] using hz
  · rintro ⟨x, hx⟩
    let x' : c.domain := ⟨x, by rw [hc]; trivial⟩
    refine ⟨c.coordinates x', ?_⟩
    simpa only [he, Homeomorph.symm_apply_apply] using hx

end HodgeLean.Foundations.QuotientDuality
