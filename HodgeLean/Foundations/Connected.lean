import HodgeLean.Foundations.Port.AlgebraicGeometry.ComplexPoint.SmoothConnected
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff

/-!
# Path connectedness of smooth integral projective complex varieties

This supplies the connectedness input downstream. HC: no distance. AV milestone: no distance.
-/

open CategoryTheory AlgebraicGeometry

namespace HodgeLean.Foundations

/-- The complex points of a smooth integral projective complex variety are path connected.
Projectivity supplies separatedness, hence quasi-separatedness.

Source: upstream `Other/AlgebraicGeometry/ComplexPoint/SmoothConnected.lean` at `2ead713`,
`ComplexPoint.connectedSpace`, and `ComplexPoint.locallyPathConnectedSpace`. -/
theorem pathConnectedSpace_complexPoint (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    PathConnectedSpace (ComplexPoint X) := by
  let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let : LocallyPathConnectedSpace (ComplexPoint X) :=
    ComplexPoint.locallyPathConnectedSpace X
  exact pathConnectedSpace_iff_connectedSpace.mpr (ComplexPoint.connectedSpace X)

end HodgeLean.Foundations

#print axioms HodgeLean.Foundations.pathConnectedSpace_complexPoint
