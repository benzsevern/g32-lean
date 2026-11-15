import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme

/-! The contravariant action of affine algebra automorphisms on complex points. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.QuotientDuality

def affineAutomorphismPointAction
    {A G : Type} [CommRing A] [Algebra ℂ A] [Group G]
    (ρ : G →* (A ≃ₐ[ℂ] A)) :
    MulAction G (ComplexPoint (Over.mk (affineSpecStructureMap A))) where
  smul g x := affineSpecComplexPointMap (ρ g⁻¹).toAlgHom x
  one_smul x := by
    change affineSpecComplexPointMap (ρ (1 : G)⁻¹).toAlgHom x = x
    apply (affineSpecEquiv A).injective
    rw [affineSpecEquiv_affineSpecComplexPointMap]
    ext a
    simp
  mul_smul g h x := by
    change affineSpecComplexPointMap (ρ (g * h)⁻¹).toAlgHom x =
      affineSpecComplexPointMap (ρ g⁻¹).toAlgHom
        (affineSpecComplexPointMap (ρ h⁻¹).toAlgHom x)
    apply (affineSpecEquiv A).injective
    simp only [affineSpecEquiv_affineSpecComplexPointMap]
    ext a
    simp

#print axioms affineAutomorphismPointAction
end HodgeLean.Foundations.QuotientDuality
