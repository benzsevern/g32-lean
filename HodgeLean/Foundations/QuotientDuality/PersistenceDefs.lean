import HodgeLean.Foundations.QuotientDuality.ComparisonAdapterDefs
import HodgeConjecture.Mathlib.Topology.Category.TopPair
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CohomologyZero

/-! # Actual pair maps for primitive persistence

The subset is the exceptional locus, rather than its complement.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The canonical map from the inverse-image pair to the target pair.
Source: Hatcher, Algebraic Topology, section 2.1, maps of pairs.
HC no distance; AV milestone no distance. -/
def persistencePairMap {X Y : TopCat.{0}} (f : X ⟶ Y) (A : Set Y) :
    TopPair.ofSubset (f ⁻¹' A) ⟶ TopPair.ofSubset A :=
  TopPair.ofSubsetHom f (fun _ hx => hx)

example (X : TopCat.{0}) (A : Set X) (x : X) :
    TopPair.Hom.fst (persistencePairMap (𝟙 X) A) x = x := rfl

/-- The actual pullback between relative singular groups in a natural degree.
Source: Hatcher, Algebraic Topology, section 3.1, relative cohomology.
HC no distance; AV milestone no distance. -/
def persistenceRelativePullback (K : Type) [CommRing K] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (A : Set Y) (n : ℕ) :=
  relativeCohomologyMap K n (persistencePairMap f A)

example (K : Type) [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y)
    (A : Set Y) (n : ℕ) : persistenceRelativePullback K f A n 0 = 0 := map_zero _

end HodgeLean.Foundations.QuotientDuality
