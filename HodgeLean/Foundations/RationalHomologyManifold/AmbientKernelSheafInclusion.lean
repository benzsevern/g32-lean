import HodgeLean.Foundations.RationalHomologyManifold.AmbientCochainSheafComplex

/-! Actual inclusion of the sheafified ambient cochain kernel.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Sheafify the original kernel inclusion as a morphism of the actual ambient cochain complexes.
Source: Bredon, Sheaf Theory, second edition, I.1 and VI.12; exact sheafification of the ambient cochain kernel.
HC no distance; AV milestone no distance.
-/
def ambientLocalZeroSheafInclusion (X : TopCat.{0}) :
    ambientLocalZeroSheafComplex X ⟶ ambientCochainSheafComplex X :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (kernel.ι (ambientCochainPresheafComplexRestriction X))

#print axioms ambientLocalZeroSheafInclusion
end HodgeLean.Foundations.RationalHomologyManifold
