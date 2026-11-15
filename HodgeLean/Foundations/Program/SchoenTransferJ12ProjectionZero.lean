import HodgeLean.Foundations.Program.SchoenTransferJ12ImageSupportZero
import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionSupport

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Singular
open AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupComparison

/-- The actual prime projection is zero outside the expected image coheight.
Source: Fulton, Intersection Theory, §19.1, support purity below its codimension. -/
theorem s4_selected_projection_prime_zero
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d s q : ℕ) (hY : TopologicalSpace.dim Y.left = d)
    (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) (h : 2 * s = 2 * d + 2 * q)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = s)
    (himage : Order.coheight ((fst A Y).left x) ≠ q) :
    s4_selected_projection A Y d (2 * q) I
      (HQ.castEquiv (A ⊗ Y) h (cycleComponentSheafClass (A ⊗ Y) x hx)) = 0 := by
  obtain ⟨c, hc⟩ := s4_selected_projection_prime_supported A Y d s q I h x hx
  have hzero := s4_selected_projection_image_support_isZero A Y d s q hY (by omega)
    x hx himage
  let S := cycleComponentAnalyticClosedSupport A ((fst A Y).left x)
  have hz := cq_support_sheaf_isZero_to_singular A S (2 * q) hzero
  letI := ModuleCat.subsingleton_of_isZero hz
  have hc0 : c = 0 := Subsingleton.elim _ _
  apply (cupComparison A (2 * q)).injective
  rw [← hc, hc0, map_zero]
  exact (cupComparison A (2 * q)).map_zero.symm

#print axioms s4_selected_projection_prime_zero

end HodgeLean.Foundations.Program
