import HodgeLean.Foundations.Program.SchoenSelectedGeometryReducedImage

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Set Topology
namespace HodgeLean.Foundations.Program

/-- A reduced subscheme with irreducible image is integral.
Source: Hartshorne, Algebraic Geometry, II.3, the reduced and irreducible criterion. -/
theorem s0_integral_of_reduced_closed_image {Y X : Scheme.{0}}
    (i : Y ⟶ X) [IsClosedImmersion i] [IsReduced Y]
    (h : IsIrreducible (range i)) : IsIntegral Y := by
  letI : IrreducibleSpace (range i) := Subtype.irreducibleSpace h
  let e := i.isClosedEmbedding.isEmbedding.toHomeomorph
  letI : IrreducibleSpace Y := e.irreducibleSpace_iff.mpr inferInstance
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

#print axioms s0_integral_of_reduced_closed_image
end HodgeLean.Foundations.Program
