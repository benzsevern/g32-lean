import HodgeLean.Foundations.RationalHomologyManifold.Defs

/-! Singular homology carries an actual retraction to a split injection.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- A continuous map with a continuous left inverse induces injective homology maps.
Source: Hatcher, Algebraic Topology, section 2.1, functoriality of singular homology.
HC no distance; AV milestone no distance.
-/
theorem homology_injective_of_retraction {X Y : TopCat.{0}}
    (j : X ⟶ Y) (r : Y ⟶ X) (h : j ≫ r = 𝟙 X) (i : ℕ) :
    Function.Injective (homologyMap ℚ i j) := by
  intro a b hab
  have hh := congrArg (homologyMap ℚ i r) hab
  change ((homologyMap ℚ i r).comp (homologyMap ℚ i j)) a =
    ((homologyMap ℚ i r).comp (homologyMap ℚ i j)) b at hh
  rw [← homologyMap_comp, h, homologyMap_id] at hh
  exact hh

#print axioms homology_injective_of_retraction
end HodgeLean.Foundations.RationalHomologyManifold
