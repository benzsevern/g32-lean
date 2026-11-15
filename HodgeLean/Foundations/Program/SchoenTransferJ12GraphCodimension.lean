import HodgeLean.Foundations.Program.SchoenTransferJ12GraphClosure
import HodgeLean.Foundations.Program.SchoenTransferJ12ProductDimension
import HodgeLean.Adapters.IntersectionProductScaf

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The target-first graph has codimension equal to the dimension of its target.
Source: Hartshorne, Algebraic Geometry, I.7 and II, Exercise 4.8. -/
theorem s4_selected_graph_codimension
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a d : ℕ) (hA : TopologicalSpace.dim A.left = a)
    (hY : TopologicalSpace.dim Y.left = d) (f : Y ⟶ A) :
    Order.coheight ((lift f (𝟙 Y)).left (genericPoint Y.left)) = a := by
  let g : Y ⟶ A ⊗ Y := lift f (𝟙 Y)
  letI : IsClosedImmersion g.left := s4_selected_graph_closed_immersion A Y f
  have hη := cq_point_height_add_coheight Y d hY (genericPoint Y.left)
  rw [coheight_genericPoint, add_zero] at hη
  have hg := IntersectionProductScaf_finite_height g.left (genericPoint Y.left)
  have hp := cq_point_height_add_coheight (A ⊗ Y) (a + d)
    (s4_selected_product_dimension A Y a d hA hY) (g.left (genericPoint Y.left))
  rw [hg, hη, Nat.cast_add, add_comm (a : ℕ∞) (d : ℕ∞)] at hp
  exact ENat.add_right_injective_of_ne_top (ENat.natCast_ne_top d) hp

#print axioms s4_selected_graph_codimension
end HodgeLean.Foundations.Program
