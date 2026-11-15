import HodgeLean.Foundations.Program.SchoenCycleAffineSpecPointPrime
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Localization

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A marked affine complex point avoiding a function lifts to its actual basic localization, with exactly the original affine point under the canonical scheme map.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_affine_localization_point_lift
    (S : Type) [CommRing S] [Algebra ℂ S] (g : S)
    (z : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap S)))
    (hg : g ∉ z.underlying.asIdeal) :
    ∃ w : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap (Localization.Away g))),
      ComplexPoint.affineSpecComplexPointMap (IsScalarTower.toAlgHom ℂ S (Localization.Away g)) w = z := by
  let ε := ComplexPoint.affineSpecEquiv S z
  have hz : (ComplexPoint.affineSpecEquiv S).symm ε = z :=
    (ComplexPoint.affineSpecEquiv S).symm_apply_apply z
  have hker : z.underlying.asIdeal = RingHom.ker ε.toRingHom := by
    rw [← hz]
    exact s2e_affine_spec_point_prime S ε
  have hne : ε g ≠ 0 := by
    intro h
    apply hg
    rw [hker]
    exact h
  let δ : Localization.Away g →ₐ[ℂ] ℂ :=
    IsLocalization.Away.liftAlgHom g (isUnit_iff_ne_zero.mpr hne)
  refine ⟨(ComplexPoint.affineSpecEquiv (Localization.Away g)).symm δ, ?_⟩
  apply (ComplexPoint.affineSpecEquiv S).injective
  rw [ComplexPoint.affineSpecEquiv_affineSpecComplexPointMap,
    Equiv.apply_symm_apply]
  ext s
  exact IsLocalization.Away.lift_eq g (isUnit_iff_ne_zero.mpr hne) s

#print axioms s2e_affine_localization_point_lift
end HodgeLean.Foundations.Program
