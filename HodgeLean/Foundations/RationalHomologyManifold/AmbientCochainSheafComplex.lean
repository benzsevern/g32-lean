import HodgeLean.Foundations.RationalHomologyManifold.AmbientCochainKernel

/-! Actual sheafified ambient cochains and their restriction to local cochains.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Sheafify the actual constant-ambient singular cochain complex in every degree.
Source: Bredon, Sheaf Theory, second edition, VI.12; ambient singular cochains and their local restriction.
HC no distance; AV milestone no distance.
-/
def ambientCochainSheafComplex (X : TopCat.{0}) : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (ambientCochainPresheafComplex X)

#print axioms ambientCochainSheafComplex
/-- Sheafify the actual local zero-cochain kernel complex.
Source: Bredon, Sheaf Theory, second edition, VI.12; the kernel of ambient cochain restriction.
HC no distance; AV milestone no distance.
-/
def ambientLocalZeroSheafComplex (X : TopCat.{0}) : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (ambientLocalZeroPresheafComplex X)

#print axioms ambientLocalZeroSheafComplex
/-- The actual sheafified ambient restriction is a map into the existing local singular cochain complex.
Source: Bredon, Sheaf Theory, second edition, VI.12; sheafification of singular cochain restriction.
HC no distance; AV milestone no distance.
-/
def ambientCochainSheafRestriction (X : TopCat.{0}) :
    ambientCochainSheafComplex X ⟶ singularCochainSheafComplex ℚ X :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (ambientCochainPresheafComplexRestriction X)

#print axioms ambientCochainSheafRestriction
end HodgeLean.Foundations.RationalHomologyManifold
