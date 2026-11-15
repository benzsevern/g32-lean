import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularFlasqueModel
import HodgeConjecture.Lemmas.AlgebraicTopology.Support.DerivedSections

/-! # The original rational injective resolution as an actual bounded complex
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original ambient constant rational injective resolution, with its actual terms retained in the full category of injective sheaves and its original zero lower bound.
Source: rationalConstantInjectiveComplex; HomologicalComplex.liftObjectProperty; CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff.
HC no distance; AV milestone no distance. -/
def properCycle_bounded_constant_injective (X : TopCat.{0}) :
    CochainComplex.Plus (InjectiveObject (TopCat.Sheaf AddCommGrpCat.{0} X)) := by
  let L := HomologicalComplex.liftObjectProperty
    (CategoryTheory.isInjective (TopCat.Sheaf AddCommGrpCat.{0} X))
    (rationalConstantInjectiveComplex X) (fun n => inferInstance)
  refine ⟨L, ⟨0, ?_⟩⟩
  rw [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _
    (InjectiveObject.ι (TopCat.Sheaf AddCommGrpCat.{0} X))]
  exact rationalConstantInjectiveComplex_isStrictlyGE X

example (X : TopCat.{0}) (n : ℤ) :
    (((InjectiveObject.ι (TopCat.Sheaf AddCommGrpCat.{0} X)).mapCochainComplexPlus.obj
      (properCycle_bounded_constant_injective X)).obj).X n =
        (rationalConstantInjectiveComplex X).X n := rfl

end HodgeLean.Foundations.QuotientDuality
