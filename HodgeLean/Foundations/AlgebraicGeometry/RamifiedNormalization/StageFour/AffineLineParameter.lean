import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme
import Mathlib.Algebra.Polynomial.AlgebraMap

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A ring element defines its actual complex affine-line parameter morphism. -/
def affineLineParameter
    {A : Type} [CommRing A] [Algebra ℂ A] (t : A) :
    Over.mk (ComplexPoint.affineSpecStructureMap A) ⟶
      Over.mk (ComplexPoint.affineSpecStructureMap (Polynomial ℂ)) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Polynomial.aeval t).toRingHom))
    (ComplexPoint.specMap_comp_affineSpecStructureMap (Polynomial.aeval t))

/-- The actual affine-line parameter retains evaluation of its original ring element. -/
theorem affineLineParameter_coordinate
    {A : Type} [CommRing A] [Algebra ℂ A] (t : A)
    (p : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap A))) :
    ComplexPoint.affineSpecEquiv (Polynomial ℂ) (Point.map (affineLineParameter t) p) Polynomial.X =
      ComplexPoint.affineSpecEquiv A p t := by
  change ComplexPoint.affineSpecEquiv (Polynomial ℂ)
    (ComplexPoint.affineSpecComplexPointMap (Polynomial.aeval t) p) Polynomial.X = _
  rw [ComplexPoint.affineSpecEquiv_affineSpecComplexPointMap]
  change (ComplexPoint.affineSpecEquiv A p) ((Polynomial.aeval t) Polynomial.X) = _
  rw [Polynomial.aeval_X]

end AlgebraicGeometry.RamifiedNormalization.StageFour
