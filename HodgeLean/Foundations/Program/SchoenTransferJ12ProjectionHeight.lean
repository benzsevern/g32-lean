import HodgeLean.Foundations.Program.SchoenTransferJ12ProductDimension

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The projection image has the expected lower coheight for a cycle on the actual product.
Source: Hartshorne, Algebraic Geometry, I.7 and III.10, dimension of a smooth projection. -/
theorem s4_selected_projection_image_coheight_ge
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d s q : ℕ) (hY : TopologicalSpace.dim Y.left = d) (hs : s = q + d)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = s) :
    (q : ℕ∞) ≤ Order.coheight ((fst A Y).left x) := by
  let a := TopologicalSpace.dim A.left
  have hsource := cq_point_height_add_coheight (A ⊗ Y) (a + d)
    (s4_selected_product_dimension A Y a d rfl hY) x
  rw [hx, hs, Nat.cast_add, Nat.cast_add, ← add_assoc] at hsource
  have hxq : Order.height x + (q : ℕ∞) = a :=
    ENat.add_left_injective_of_ne_top (ENat.natCast_ne_top d) hsource
  have hfinite : Order.height x ≠ ⊤ := by
    intro ht
    rw [ht, top_add] at hxq
    exact (ENat.natCast_ne_top a) hxq.symm
  have hbase := cq_point_height_add_coheight A a rfl ((fst A Y).left x)
  have hle : Order.height x + (q : ℕ∞) ≤
      Order.height x + Order.coheight ((fst A Y).left x) := by
    calc
      Order.height x + (q : ℕ∞) = a := hxq
      _ = Order.height ((fst A Y).left x) + Order.coheight ((fst A Y).left x) := hbase.symm
      _ ≤ _ := add_le_add (cq_height_image_le (fst A Y) x) le_rfl
  exact (ENat.add_le_add_iff_left hfinite).mp hle

#print axioms s4_selected_projection_image_coheight_ge

end HodgeLean.Foundations.Program
