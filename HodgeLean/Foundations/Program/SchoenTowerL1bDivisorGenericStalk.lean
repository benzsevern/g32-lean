import HodgeLean.Foundations.Program.SchoenTowerL1bKummerGermPullback

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Actual generic pullback extends the stalk map at every source point. -/
theorem s2v_l1b_divisor_generic_stalk
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (p : X) (v : Y.presheaf.stalk (f p)) :
    s2v_l1b_functionFieldPullback f
      (algebraMap (Y.presheaf.stalk (f p)) Y.functionField v) =
      algebraMap (X.presheaf.stalk p) X.functionField ((f.stalkMap p).hom v) := by
  let gx := genericPoint X
  let gy := genericPoint Y
  have hg : f gx = gy := s2_dominant_genericPoint f
  have hx : gx ⤳ p := (genericPoint_spec X).specializes trivial
  have hy : gy ⤳ f p := (genericPoint_spec Y).specializes trivial
  have ht : Y.presheaf.stalkSpecializes hy ≫
      eqToHom (congrArg (fun y => Y.presheaf.stalk y) hg.symm) =
      Y.presheaf.stalkSpecializes (f.base.hom.map_specializes hx) := by
    have htransport {g' : Y} (hg' : g' = gy) (h' : g' ⤳ f p) :
        Y.presheaf.stalkSpecializes hy ≫
          eqToHom (congrArg (fun y => Y.presheaf.stalk y) hg'.symm) =
        Y.presheaf.stalkSpecializes h' := by
      subst g'
      simp only [eqToHom_refl, Category.comp_id]
    exact htransport hg _
  have hsquare : Y.presheaf.stalkSpecializes hy ≫ s2v_l1b_functionFieldPullback f =
      f.stalkMap p ≫ X.presheaf.stalkSpecializes hx := by
    rw [s2v_l1b_functionFieldPullback, ← Category.assoc, ht, f.stalkSpecializes_stalkMap]
  exact congrArg (fun h : Y.presheaf.stalk (f p) ⟶ X.functionField => h.hom v) hsquare

/-- A specified generic spectrum square determines the actual function-field inclusion. -/
theorem s2v_l1b_divisor_generic_map
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (κ : Y.functionField ⟶ X.functionField)
    (hκ : Spec.map κ ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ f) :
    κ = s2v_l1b_functionFieldPullback f := by
  apply Spec.map_injective
  apply (cancel_mono (Y.fromSpecStalk (genericPoint Y))).mp
  rw [hκ, s2v_l1b_functionFieldPullback_generic_square]

end HodgeLean.Foundations.Program
