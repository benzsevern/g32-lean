import HodgeLean.Foundations.Program.SchoenCycleC1SectionFieldTowerHelpers

/-! # The retained generic field embedding and every actual local stalk map -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The projection's specified generic stalk transport commutes with its
actual local stalk pullback and the canonical local fraction embeddings. -/
theorem s2e_c1_generic_stalk_map_local_square
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    (hg : f (genericPoint X) = genericPoint Y) (p : X)
    (r : Y.presheaf.stalk (f p)) :
    (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫ f.stalkMap (genericPoint X)).hom
        (algebraMap (Y.presheaf.stalk (f p)) Y.functionField r) =
      algebraMap (X.presheaf.stalk p) X.functionField ((f.stalkMap p).hom r) := by
  have hX : genericPoint X ⤳ p := (genericPoint_spec X).specializes trivial
  have hY : genericPoint Y ⤳ f p := (genericPoint_spec Y).specializes trivial
  have htransport (a b c : Y) (h : a = b) (ha : a ⤳ c) (hb : b ⤳ c) :
      Y.presheaf.stalkSpecializes hb ≫ eqToHom (congrArg Y.presheaf.stalk h.symm) =
        Y.presheaf.stalkSpecializes ha := by
    subst b
    simp only [eqToHom_refl, Category.comp_id]
  have he : Y.presheaf.stalkSpecializes hY ≫
      eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫ f.stalkMap (genericPoint X) =
      f.stalkMap p ≫ X.presheaf.stalkSpecializes hX := by
    rw [← Category.assoc, htransport (f (genericPoint X)) (genericPoint Y) (f p)
      hg (hX.map f.continuous) hY]
    exact f.stalkSpecializes_stalkMap (genericPoint X) p hX
  exact congrArg (fun k => k.hom r) he

end HodgeLean.Foundations.Program
