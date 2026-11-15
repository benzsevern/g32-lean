import HodgeLean.Adapters.NormalConeB4aGysinBoundaryDimension

noncomputable section
namespace HodgeLean.Adapters
open AlgebraicGeometry TopologicalSpace

/-- The reduced scheme on a closed subset has exactly the topological dimension
of that closed subspace. -/
theorem a3b4a_gysin_reduced_closed_dimension_eq
    {Z : Scheme.{0}} (S : Closeds Z) :
    topologicalKrullDim (reducedClosedSubscheme S) = topologicalKrullDim (S : Set Z) := by
  let e : reducedClosedSubscheme S ≃ₜ (S : Set Z) :=
    (reducedClosedSubschemeι S).isClosedEmbedding.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (range_reducedClosedSubschemeι S))
  exact IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph

end HodgeLean.Adapters
