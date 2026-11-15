import HodgeLean.Foundations.Program.SchoenTransferJ12GraphCodimension

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A component on the source acquires the target dimension as additional codimension in the graph.
Source: Hartshorne, Algebraic Geometry, I.7, dimension of a closed immersion image. -/
theorem s4_selected_graph_point_codimension
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a d : ℕ) (hA : TopologicalSpace.dim A.left = a)
    (hY : TopologicalSpace.dim Y.left = d) (f : Y ⟶ A)
    (z : Y.left) (p : ℕ) (hz : Order.coheight z = p) :
    Order.coheight ((lift f (𝟙 Y)).left z) = a + p := by
  let g : Y ⟶ A ⊗ Y := lift f (𝟙 Y)
  letI : IsClosedImmersion g.left := s4_selected_graph_closed_immersion A Y f
  have hy := cq_point_height_add_coheight Y d hY z
  rw [hz] at hy
  have hfinite : Order.height z ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top d) ((le_self_add).trans_eq hy)
  have hg := IntersectionProductScaf_finite_height g.left z
  have hp := cq_point_height_add_coheight (A ⊗ Y) (a + d)
    (s4_selected_product_dimension A Y a d hA hY) (g.left z)
  rw [hg, Nat.cast_add] at hp
  apply ENat.add_right_injective_of_ne_top hfinite
  calc
    Order.height z + Order.coheight (g.left z) = (a : ℕ∞) + d := hp
    _ = (a : ℕ∞) + (Order.height z + p) := congrArg (fun t : ℕ∞ => (a : ℕ∞) + t) hy.symm
    _ = Order.height z + ((a : ℕ∞) + p) := by ac_rfl

#print axioms s4_selected_graph_point_codimension
end HodgeLean.Foundations.Program
