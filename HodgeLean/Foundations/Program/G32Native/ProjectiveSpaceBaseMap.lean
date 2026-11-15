import HodgeConjecture.Definitions.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Pullbacks

/-! Base maps of the fixed polynomial projective-space construction. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The morphism of projective spaces induced by a map of bases. -/
def g32l4_projectiveSpace_baseMap {S T : Scheme.{0}} (K : Type) (f : S ⟶ T) :
    ProjectiveSpace K S ⟶ ProjectiveSpace K T :=
  pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (Subsingleton.elim _ _) (by simp)

instance {S T : Scheme.{0}} (K : Type) (f : S ⟶ T) [IsOpenImmersion f] :
    IsOpenImmersion (g32l4_projectiveSpace_baseMap K f) := by
  unfold g32l4_projectiveSpace_baseMap
  apply Scheme.pullback_map_isOpenImmersion

end HodgeLean.Foundations.Program
