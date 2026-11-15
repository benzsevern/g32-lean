import HodgeLean.Foundations.Program.SchoenTowerL1bTransportStalkAction

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Fixed-stalk pullback respects composition of dominant maps at their shared fixed point. -/
theorem s2v_l1b_divisor_fixed_stalk_comp
    (X : Scheme.{0}) [IsIntegral X] (f g : X ⟶ X)
    [IsDominant f] [IsDominant g] (p : X) (hf : f p = p) (hg : g p = p)
    (hfg : (f ≫ g) p = p) (v : X.presheaf.stalk p) :
    s2e_fixed_point_stalkPullback X (f ≫ g) p hfg v =
      s2e_fixed_point_stalkPullback X f p hf
        (s2e_fixed_point_stalkPullback X g p hg v) := by
  apply IsFractionRing.injective (X.presheaf.stalk p) X.functionField
  rw [← s2v_l1b_transport_generic_stalk_pullback,
    ← s2v_l1b_transport_generic_stalk_pullback,
    ← s2v_l1b_transport_generic_stalk_pullback,
    s2v_l1b_functionFieldPullback_comp]
  rfl

/-- The identity map acts trivially on the actual fixed stalk. -/
theorem s2v_l1b_divisor_fixed_stalk_id
    (X : Scheme.{0}) [IsIntegral X] (p : X) (hp : (𝟙 X) p = p)
    (v : X.presheaf.stalk p) :
    s2e_fixed_point_stalkPullback X (𝟙 X) p hp v = v := by
  apply IsFractionRing.injective (X.presheaf.stalk p) X.functionField
  rw [← s2v_l1b_transport_generic_stalk_pullback, s2v_l1b_functionFieldPullback_id]
  rfl

end HodgeLean.Foundations.Program
