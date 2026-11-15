import HodgeLean.Foundations.QuotientDuality.MonomialRootSpecSmooth
import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.CoordinateRootCover

/-! Smoothness of a root component from its actual parameter compatibility. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.TameMonomialCover.Helpers
namespace HodgeLean.Foundations.QuotientDuality

theorem monomial_root_parameter_spec_smooth
    (k R A : Type) [CommRing k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra R A] [Algebra k A] [IsScalarTower k R A]
    (n m : ℕ) (c : MvPolynomial (Fin n) k →ₐ[k] R)
    (b : ULift.{0} (MvPolynomial (Fin n) k) →+* A) (hb : b.Etale)
    (hparam : b.comp (rootParameterMap k n m).toRingHom =
      (algebraMap R A).comp c.toRingHom) :
    SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
  apply etale_lifted_polynomial_spec_smooth k A n b hb
  intro t
  have hc : rootParameterMap k n m (MvPolynomial.C t) =
      ULift.up (MvPolynomial.C t) := by
    rw [rootParameterMap, AlgHom.comp_apply, MvPolynomial.expand_C]
    rfl
  have H := RingHom.congr_fun hparam (MvPolynomial.C t)
  change b (rootParameterMap k n m (MvPolynomial.C t)) =
    algebraMap R A (c (MvPolynomial.C t)) at H
  have hc' : c (MvPolynomial.C t) = algebraMap k R t := c.commutes t
  rw [hc, hc'] at H
  exact H.trans (IsScalarTower.algebraMap_apply k R A t).symm

#print axioms monomial_root_parameter_spec_smooth
end HodgeLean.Foundations.QuotientDuality
