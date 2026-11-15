import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The canonical actual basic-localization map is injective on complex points, retaining equality of the entire marked point from equality of its affine image.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_affine_localization_point_map_injective
    (S : Type) [CommRing S] [Algebra ℂ S] (g : S) :
    Function.Injective (ComplexPoint.affineSpecComplexPointMap
      (IsScalarTower.toAlgHom ℂ S (Localization.Away g))) := by
  intro u v h
  apply (ComplexPoint.affineSpecEquiv (Localization.Away g)).injective
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers g)
  ext s
  change ComplexPoint.affineSpecEquiv (Localization.Away g) u (algebraMap S (Localization.Away g) s) =
    ComplexPoint.affineSpecEquiv (Localization.Away g) v (algebraMap S (Localization.Away g) s)
  have he := congrArg (fun z => ComplexPoint.affineSpecEquiv S z s) h
  simpa only [ComplexPoint.affineSpecEquiv_affineSpecComplexPointMap, AlgHom.comp_apply,
    IsScalarTower.toAlgHom_apply] using he

#print axioms s2e_affine_localization_point_map_injective
end HodgeLean.Foundations.Program
