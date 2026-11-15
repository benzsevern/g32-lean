import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme

/-! Actual affine scheme isomorphisms associated to complex algebra automorphisms. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.QuotientDuality

def affineAlgebraAutomorphismIso
    {A : Type} [CommRing A] [Algebra ℂ A] (e : A ≃ₐ[ℂ] A) :
    Over.mk (affineSpecStructureMap A) ≅ Over.mk (affineSpecStructureMap A) :=
  Over.isoMk (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op)
    (specMap_comp_affineSpecStructureMap e.toAlgHom)

#print axioms affineAlgebraAutomorphismIso
end HodgeLean.Foundations.QuotientDuality
