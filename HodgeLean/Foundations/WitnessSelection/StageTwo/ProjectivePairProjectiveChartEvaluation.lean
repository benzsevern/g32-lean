import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Projective

/-! Standard projective charts at affine polynomial evaluation points.

HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.WitnessSelection.StageTwo

/-- A vector with one coordinate equal to one is represented by the corresponding affine chart evaluation.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_projective_chart_evaluation {n : ℕ}
    (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) (i : Fin (n + 1)) (hi : v i = 1) :
    (Spec.map (CommRingCat.ofHom (MvPolynomial.eval v)) ≫
      (AffineSpace.SpecIso (Fin (n + 1)) ↧ℂ).inv) ≫
        ComplexProjectiveSpace.chartAffineToProjectiveSpace i =
      (ComplexProjectiveSpace.vectorToComplexPoint v hv).left := by
  classical
  have hvi : v i ≠ 0 := by rw [hi]; exact one_ne_zero
  let a := ComplexProjectiveSpace.vectorChartToAffinePoint i ⟨v, hvi⟩
  have hr : ComplexProjectiveSpace.vectorChartRatios i ⟨v, hvi⟩ = v := by
    change (v i)⁻¹ • v = v
    rw [hi, inv_one, one_smul]
  have ha := ComplexProjectiveSpace.vectorChartToAffinePoint_comp_SpecIso i ⟨v, hvi⟩
  rw [hr] at ha
  change a.left ≫ (AffineSpace.SpecIso (Fin (n + 1)) ↧ℂ).hom =
    Spec.map (CommRingCat.ofHom (MvPolynomial.eval v)) at ha
  rw [← ha]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg (fun p => p.left)
    (ComplexProjectiveSpace.chartVectorToComplexPoint_eq i ⟨v, hvi⟩)

end HodgeLean.WitnessSelection.StageTwo
