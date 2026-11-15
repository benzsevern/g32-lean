import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.AffineLineParameter

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A point lies in the specified actual affine-parameter fibre exactly when its original parameter evaluates to that scalar. -/
theorem affineLineParameter_fibre_iff
    {A : Type} [CommRing A] [Algebra ℂ A] (t : A)
    (p : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap A))) (c : ℂ) :
    Point.map (affineLineParameter t) p =
      (ComplexPoint.affineSpecEquiv (Polynomial ℂ)).symm (Polynomial.aeval c) ↔
        ComplexPoint.affineSpecEquiv A p t = c := by
  constructor
  · intro h
    have he := congrArg (fun q => ComplexPoint.affineSpecEquiv (Polynomial ℂ) q Polynomial.X) h
    rw [affineLineParameter_coordinate, Equiv.apply_symm_apply, Polynomial.aeval_X] at he
    exact he
  · intro h
    apply (ComplexPoint.affineSpecEquiv (Polynomial ℂ)).injective
    rw [Equiv.apply_symm_apply]
    apply Polynomial.algHom_ext
    rw [affineLineParameter_coordinate, Polynomial.aeval_X, h]

end AlgebraicGeometry.RamifiedNormalization.StageFour
