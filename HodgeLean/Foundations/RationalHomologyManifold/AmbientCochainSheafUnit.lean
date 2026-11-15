import HodgeLean.Foundations.RationalHomologyManifold.AmbientCochainUnit

/-! The actual ambient cup unit after sheafification.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Sheafify the scalar multiples of the actual ambient singular cup unit.
Source: Hatcher, Algebraic Topology, section 3.2; Bredon, Sheaf Theory, second edition, I.1.
HC no distance; AV milestone no distance.
-/
def ambientConstantsToZeroSheaf (X : TopCat.{0}) :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
      ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of ℚ)) ⟶
        (ambientCochainSheafComplex X).X 0 :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).map
    (ambientConstantsToZeroPresheaf X)

#print axioms ambientConstantsToZeroSheaf
/-- The sheafified actual cup unit remains a degree-zero ambient cocycle.
Source: Hatcher, Algebraic Topology, section 3.2; Bredon, Sheaf Theory, second edition, I.1.
HC no distance; AV milestone no distance.
-/
theorem ambientConstantsToZeroSheaf_coboundary (X : TopCat.{0}) :
    ambientConstantsToZeroSheaf X ≫ (ambientCochainSheafComplex X).d 0 1 = 0 := by
  let F := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}
  change F.map (ambientConstantsToZeroPresheaf X) ≫
    F.map ((ambientCochainPresheafComplex X).d 0 1) = 0
  rw [← F.map_comp, ambientConstantsToZeroPresheaf_coboundary, F.map_zero]

#print axioms ambientConstantsToZeroSheaf_coboundary
end HodgeLean.Foundations.RationalHomologyManifold
