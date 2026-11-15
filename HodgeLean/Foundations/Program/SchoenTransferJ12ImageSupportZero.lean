import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionHeight
import HodgeLean.Foundations.Program.CompensationAssemblySpan2Local

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory.Limits
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Purity annihilates the projected support group when its actual coheight exceeds the target degree.
Source: Fulton, Intersection Theory, §19.1; the normalized support purity comparison. -/
theorem s4_selected_projection_image_support_isZero
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d s q : ℕ) (hY : TopologicalSpace.dim Y.left = d) (hs : s = q + d)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = s)
    (himage : Order.coheight ((fst A Y).left x) ≠ q) :
    IsZero (AddCommGrpCat.of
      (H_[cycleComponentAnalyticClosedSupport A ((fst A Y).left x)]^(2 * q)(A; ℚ))) := by
  let y := (fst A Y).left x
  let a := TopologicalSpace.dim A.left
  have hsum := cq_point_height_add_coheight A a rfl y
  have hbound : Order.coheight y ≤ a := by
    calc
      Order.coheight y ≤ Order.height y + Order.coheight y := le_add_self
      _ = a := hsum
  have hfinite : Order.coheight y ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top a) hbound
  obtain ⟨p, hp⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hge := s4_selected_projection_image_coheight_ge A Y d s q hY hs x hx
  have hgt : (q : ℕ∞) < Order.coheight y := lt_of_le_of_ne hge himage.symm
  rw [← hp] at hgt
  have hpgt : q < p := by exact_mod_cast hgt
  exact cq_prime_support_isZero_of_lt A y hp.symm (2 * q) (by omega)

#print axioms s4_selected_projection_image_support_isZero

end HodgeLean.Foundations.Program
