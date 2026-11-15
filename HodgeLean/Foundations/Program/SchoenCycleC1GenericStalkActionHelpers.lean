import HodgeLean.Foundations.Program.SchoenCycleC1FunctionFieldActionHelpers

/-! # The actual generic stalk embedding in the deck action -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The generic stalk map of the actual projection retains its generic
scheme square, including transport to the specified base generic point. -/
theorem s2e_c1_genericStalkMap_square
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    (hg : f (genericPoint X) = genericPoint Y) :
    Spec.map (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫
      f.stalkMap (genericPoint X)) ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ f := by
  have htransport (x y : Y) (h : x = y) :
      Spec.map (eqToHom (congrArg Y.presheaf.stalk h.symm)) ≫
        Y.fromSpecStalk y = Y.fromSpecStalk x := by
    subst y
    simp only [eqToHom_refl, Spec.map_id, Category.id_comp]
  rw [Spec.map_comp, Category.assoc, htransport,
    Scheme.SpecMap_stalkMap_fromSpecStalk]
  exact hg

/-- The projection's actual generic stalk embedding supplies its
function-field automorphism representation over the base field. -/
def s2e_c1_genericStalkDeckHom
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    (hg : f (genericPoint X) = genericPoint Y) :
    let φ := (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫
      f.stalkMap (genericPoint X)).hom
    letI := φ.toAlgebra
    Aut (Over.mk f) →* (X.functionField ≃ₐ[Y.functionField] X.functionField) :=
  s2e_c1_deckFunctionFieldHom f _ (s2e_c1_genericStalkMap_square f hg)

end HodgeLean.Foundations.Program
