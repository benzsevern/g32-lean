import HodgeLean.Foundations.Program.SchoenTransferJ12GraphClosure
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory TopologicalSpace
open CategoryTheory.CartesianMonoidalCategory
namespace HodgeLean.Foundations.Program

/-- The analytic support of a component in the graph is the actual graph image of its source support.
Source: Hartshorne, Algebraic Geometry, II.3, closed immersions and closures. -/
theorem s4_selected_graph_component_support
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) (z : Y.left) :
    (cycleComponentAnalyticClosedSupport (A ⊗ Y) ((lift f (𝟙 Y)).left z) :
      Set (ComplexPoint (A ⊗ Y))) =
      Point.map (lift f (𝟙 Y)) '' (cycleComponentAnalyticClosedSupport Y z :
        Set (ComplexPoint Y)) := by
  let g : Y ⟶ A ⊗ Y := lift f (𝟙 Y)
  letI : IsClosedImmersion g.left := s4_selected_graph_closed_immersion A Y f
  have hcl : closure ({g.left z} : Set (A ⊗ Y).left) = g.left '' closure {z} := by
    rw [← Set.image_singleton]
    exact g.left.isClosedEmbedding.closure_image_eq _
  ext a
  change a.underlying ∈ closure {g.left z} ↔ _
  rw [hcl]
  constructor
  · rintro ⟨b, hb, hba⟩
    have har : a ∈ Set.range (Point.map g) := by
      rw [range_map_of_closedImmersion g]
      exact ⟨b, hba⟩
    obtain ⟨b', rfl⟩ := har
    have hb' : b'.underlying = b := g.left.isClosedEmbedding.injective
      ((Point.underlying_map g b').symm.trans hba.symm)
    exact ⟨b', (show b'.underlying ∈ closure {z} from hb'.symm ▸ hb), rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b.underlying, hb, (Point.underlying_map g b).symm⟩

#print axioms s4_selected_graph_component_support
end HodgeLean.Foundations.Program
