import HodgeLean.RealDefs.Port.AlgebraicTopology.Sheaf.HomologySection
import HodgeConjecture.Definitions.AlgebraicTopology.Support.SectionRestrictionCone

/-! # Original finite singular chains as actual relative-chain sheaf sections
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular TopologicalSpace Opposite
namespace HodgeLean.Foundations.QuotientDuality

/-- Project actual finite singular chains to the original open-complement pair and then take their sections under the original chain sheafification unit.
Source: relativeChainProjection; singularChainPresheafComplexEvaluationIso; singularChainSheafificationUnit; Bredon, Sheaf Theory, second edition, V.9.
HC no distance; AV milestone no distance. -/
def properCycle_chain_sheaf_section_map (X : TopCat.{0}) (U : Opens X) :
    ((forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).mapHomologicalComplex (.down ℕ)).obj
        (SingularChainComplex ℚ X) ⟶
      ((TopCat.Sheaf.supportEvaluation X U).mapHomologicalComplex (.down ℕ)).obj
        (singularChainSheafComplex ℚ X) :=
  ((forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).mapHomologicalComplex (.down ℕ)).map
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)) ≫
    (singularChainPresheafComplexEvaluationIso ℚ X U).inv ≫
      (((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (op U)).mapHomologicalComplex
        (.down ℕ)).map (singularChainSheafificationUnit ℚ X)

example (X : TopCat.{0}) (U : Opens X) (n : ℕ)
    (c : (SingularChainComplex ℚ X).X n) :
    (properCycle_chain_sheaf_section_map X U).f n c =
      (toSheafify (Opens.grothendieckTopology X) (singularChainPresheaf ℚ X n)).app (op U)
        ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n c) := by
  rfl

end HodgeLean.Foundations.QuotientDuality
