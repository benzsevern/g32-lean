import HodgeLean.Foundations.Program.SchoenTransferJ12Graph

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory TopologicalSpace
open CategoryTheory.CartesianMonoidalCategory
namespace HodgeLean.Foundations.Program

/-- The closure of the actual graph generic point is precisely the range of its graph morphism.
Source: Hartshorne, Algebraic Geometry, II.3 and II, Exercise 4.8. -/
theorem s4_selected_graph_generic_closure
    (A Y : Over (Spec ↧ℂ)) [IsSeparated A.hom] [IsIntegral Y.left]
    (f : Y ⟶ A) :
    closure ({(lift f (𝟙 Y)).left (genericPoint Y.left)} : Set (A ⊗ Y).left) =
      Set.range (lift f (𝟙 Y)).left := by
  let g : Y ⟶ A ⊗ Y := lift f (𝟙 Y)
  letI : IsClosedImmersion g.left := s4_selected_graph_closed_immersion A Y f
  apply le_antisymm
  · apply closure_minimal
    · exact Set.singleton_subset_iff.mpr ⟨genericPoint Y.left, rfl⟩
    · exact g.left.isClosedEmbedding.isClosed_range
  · have h := image_closure_subset_closure_image (f := g.left)
      (s := ({genericPoint Y.left} : Set Y.left)) g.left.continuous
    simpa only [genericPoint_closure, Set.image_univ, Set.image_singleton] using h

#print axioms s4_selected_graph_generic_closure

end HodgeLean.Foundations.Program
