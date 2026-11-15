import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorStalkSpectrum

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Specialization from a stalk prime agrees with the actual localization map under the canonical stalk isomorphism. -/
theorem s2v_l1b_divisor_specialization_localization
    (X : Scheme.{0}) [IsIntegral X] (x : X) (z : Spec (X.presheaf.stalk x))
    (h : (X.fromSpecStalk x) z ⤳ x) :
    StructureSheaf.toStalk (X.presheaf.stalk x) z =
        X.presheaf.stalkSpecializes h ≫ (X.fromSpecStalk x).stalkMap z := by
  apply Spec.map_injective
  apply (cancel_mono (X.fromSpecStalk x)).mp
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]
  congr 1
  exact (Spec.fromSpecStalk_eq' _ _).symm

end HodgeLean.Foundations.Program
