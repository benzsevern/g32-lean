import HodgeLean.Foundations.Program.SchoenTowerL1bKummerGermPullback
import HodgeLean.Foundations.Program.SchoenCycleFixedStalkAction

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Pullback on the actual function field extends the transported pullback at every fixed stalk. -/
theorem s2v_l1b_transport_generic_stalk_pullback
    (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ X) [IsDominant f]
    (p : X) (hp : f p = p) (v : X.presheaf.stalk p) :
    s2v_l1b_functionFieldPullback f (algebraMap (X.presheaf.stalk p) X.functionField v) =
      algebraMap (X.presheaf.stalk p) X.functionField
        (s2e_fixed_point_stalkPullback X f p hp v) := by
  let g := genericPoint X
  have hg : f g = g := s2_dominant_genericPoint f
  have hgp : g ⤳ p := (genericPoint_spec X).specializes trivial
  have ht : X.presheaf.stalkSpecializes hgp ≫
      eqToHom (congrArg (fun y => X.presheaf.stalk y) hg.symm) =
      (X.presheaf.stalkCongr (.of_eq hp)).inv ≫
        X.presheaf.stalkSpecializes (f.base.hom.map_specializes hgp) := by
    have htransport {g' p' : X} (hg' : g' = g) (hp' : p' = p) (h' : g' ⤳ p') :
        X.presheaf.stalkSpecializes hgp ≫
          eqToHom (congrArg (fun y => X.presheaf.stalk y) hg'.symm) =
        (X.presheaf.stalkCongr (.of_eq hp')).inv ≫ X.presheaf.stalkSpecializes h' := by
      subst g'
      subst p'
      simp only [eqToHom_refl, Category.comp_id, TopCat.Presheaf.stalkCongr_inv,
        TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
    exact htransport hg hp _
  have hsquare : X.presheaf.stalkSpecializes hgp ≫ s2v_l1b_functionFieldPullback f =
      (X.presheaf.stalkCongr (.of_eq hp)).inv ≫ f.stalkMap p ≫
        X.presheaf.stalkSpecializes hgp := by
    rw [s2v_l1b_functionFieldPullback, ← Category.assoc, ht,
      Category.assoc, f.stalkSpecializes_stalkMap]
  exact congrArg (fun h : X.presheaf.stalk p ⟶ X.functionField => h.hom v) hsquare

end HodgeLean.Foundations.Program
