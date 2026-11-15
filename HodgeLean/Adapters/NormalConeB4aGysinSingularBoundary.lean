import HodgeLean.Adapters.NormalConeB4aGysinBoundaryDimension

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- The singular boundary of a reduced Noetherian complex scheme has strictly
smaller dimension, including when the scheme has several components. -/
theorem a3b4a_gysin_reduced_singular_boundary_dimension_lt
    {Z : Scheme.{0}} [IsNoetherian Z] [IsReduced Z]
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q]
    (n : ℕ) (hdim : topologicalKrullDim Z ≤ (n : ℕ)) :
    topologicalKrullDim (reducedSingularLocus q) < (n : ℕ) := by
  apply a3b4a_gysin_boundary_dimension_lt_of_generic_avoidance (singularLocusClosed q) n hdim
  intro ξ hξ
  intro hbad
  exact hbad (a3b4a_gysin_generic_points_mem_dense_open (q.smoothLocus : Set Z)
    q.smoothLocus.isOpen q.dense_smoothLocus_of_perfectField ξ hξ)

end HodgeLean.Adapters
