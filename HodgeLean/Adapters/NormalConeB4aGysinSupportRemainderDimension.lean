import HodgeLean.Adapters.NormalConeB4aGysinSingularBoundary
import HodgeLean.Adapters.NormalConeB4aGysinReducedClosedDimension

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- The first closed remainder of the actual reduced support filtration has
strictly smaller dimension, even when that support is reducible. -/
theorem a3b4a_gysin_support_remainder_dimension_lt
    {Z : Scheme.{0}} [IsNoetherian Z]
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q]
    (S : Closeds Z) (n : ℕ)
    (hdim : topologicalKrullDim (reducedClosedSubscheme S) ≤ (n : ℕ)) :
    topologicalKrullDim (reducedClosedSubscheme (reducedClosedSingularRemainder q S)) <
      (n : ℕ) := by
  letI : NoetherianSpace (reducedClosedSubscheme S) :=
    (reducedClosedSubschemeι S).isClosedEmbedding.isInducing.noetherianSpace
  letI : IsLocallyNoetherian (reducedClosedSubscheme S) :=
    LocallyOfFiniteType.isLocallyNoetherian (reducedClosedStructureMap q S)
  letI : IsNoetherian (reducedClosedSubscheme S) := {}
  have hs := a3b4a_gysin_reduced_singular_boundary_dimension_lt
    (reducedClosedStructureMap q S) n hdim
  change topologicalKrullDim (reducedClosedSubscheme
    (singularLocusClosed (reducedClosedStructureMap q S))) < (n : ℕ) at hs
  rw [a3b4a_gysin_reduced_closed_dimension_eq] at hs
  let e := (reducedClosedSubschemeι S).isClosedEmbedding.isEmbedding.homeomorphImage
    ((singularLocusClosed (reducedClosedStructureMap q S)) : Set (reducedClosedSubscheme S))
  calc
    topologicalKrullDim (reducedClosedSubscheme (reducedClosedSingularRemainder q S)) =
        topologicalKrullDim (reducedClosedSingularRemainder q S : Set Z) :=
      a3b4a_gysin_reduced_closed_dimension_eq _
    _ = topologicalKrullDim
        ((singularLocusClosed (reducedClosedStructureMap q S)) : Set (reducedClosedSubscheme S)) :=
      (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).symm
    _ < (n : ℕ) := hs

end HodgeLean.Adapters
