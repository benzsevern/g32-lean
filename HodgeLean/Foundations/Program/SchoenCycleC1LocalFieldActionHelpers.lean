import HodgeLean.Foundations.Program.SchoenCycleStep1Field
import HodgeLean.Foundations.Program.SchoenCycleFixedStalkScalars

/-! # Compatibility of actual fixed-point and generic field pullback -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The actual pullback on the fixed-point local ring agrees with generic
rational-function pullback under the canonical local fraction embedding. -/
theorem s2e_c1_fieldPullback_local_stalk
    (X : Scheme) [IsIntegral X] (f : X ⟶ X) [IsIso f]
    (p : X) (hp : f p = p) (r : X.presheaf.stalk p) :
    s2e_step1_fieldPullback X f (algebraMap (X.presheaf.stalk p) X.functionField r) =
      algebraMap (X.presheaf.stalk p) X.functionField
        (s2e_fixed_point_stalkPullback X f p hp r) := by
  have h : genericPoint X ⤳ p := (genericPoint_spec X).specializes trivial
  have he : X.presheaf.stalkSpecializes h ≫
      (X.presheaf.stalkCongr (.of_eq (genericPoint_eq_of_isOpenImmersion f))).inv ≫
        f.stalkMap (genericPoint X) =
      (X.presheaf.stalkCongr (.of_eq hp)).inv ≫ f.stalkMap p ≫
        X.presheaf.stalkSpecializes h := by
    rw [← f.stalkSpecializes_stalkMap (genericPoint X) p h]
    simp only [TopCat.Presheaf.stalkCongr_inv, ← Category.assoc,
      TopCat.Presheaf.stalkSpecializes_comp]
  exact congrArg (fun k => k.hom r) he

end HodgeLean.Foundations.Program
