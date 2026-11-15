import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSurfaceOrientation

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- The scalar complex coordinate identifies the plane pair with the
one-coordinate complex model pair. -/
def s2v_l1b_action_scalar_pair_iso :
    pointComplementPair (0 : ℂ) ≅ puncturedPair ℂ 1 :=
  TopPair.isoOfSubset b6m_surfaceCoordinateEquiv.toHomeomorph (fun z => by
    change b6m_surfaceCoordinateEquiv z ≠ 0 ↔ z ≠ 0
    simpa only [map_zero] using
      (show b6m_surfaceCoordinateEquiv z ≠ b6m_surfaceCoordinateEquiv 0 ↔ z ≠ 0
        from b6m_surfaceCoordinateEquiv.injective.ne_iff))

/-- The standard one-coordinate complex class written in the scalar plane. -/
def s2v_l1b_action_scalarLocalClass (R : Type) [CommRing R] :
    RelativeHomology R (pointComplementPair (0 : ℂ)) 2 :=
  relativeHomologyMap R 2 s2v_l1b_action_scalar_pair_iso.inv (standardComplexLocalClass R 1)

/-- Conversion back to the one-coordinate model retains its exact class. -/
theorem s2v_l1b_action_scalarLocalClass_normalization (R : Type) [CommRing R] :
    relativeHomologyMap R 2 s2v_l1b_action_scalar_pair_iso.hom
      (s2v_l1b_action_scalarLocalClass R) = standardComplexLocalClass R 1 := by
  rw [s2v_l1b_action_scalarLocalClass, ← LinearMap.comp_apply,
    ← relativeHomologyMap_comp, Iso.inv_hom_id, relativeHomologyMap_id, LinearMap.id_apply]

end HodgeLean.Foundations.Program
