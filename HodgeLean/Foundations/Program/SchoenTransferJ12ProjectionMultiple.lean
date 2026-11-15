import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionSupport
import HodgeLean.Foundations.Program.CompensationAssemblySpan2Local

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Singular
open AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupComparison

/-- In the expected coheight the projected prime class is a rational multiple of its actual image class.
Source: Fulton, Intersection Theory, §19.1; rank one of the normalized support class. -/
theorem s4_selected_projection_prime_multiple
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d s q : ℕ) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ)
    (h : 2 * s = 2 * d + 2 * q)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = s)
    (himage : Order.coheight ((fst A Y).left x) = q) :
    ∃ r : ℚ, s4_selected_projection A Y d (2 * q) I
        (HQ.castEquiv (A ⊗ Y) h (cycleComponentSheafClass (A ⊗ Y) x hx)) =
      r • cycleComponentSheafClass A ((fst A Y).left x) himage := by
  obtain ⟨c, hc⟩ := s4_selected_projection_prime_supported A Y d s q I h x hx
  obtain ⟨r, hr⟩ := cq_span_relative_multiple A ((fst A Y).left x) q himage c
  refine ⟨r, ?_⟩
  apply (cupComparison A (2 * q)).injective
  rw [← hc, hr, map_smul]
  rw [(cupComparison A (2 * q)).map_smul r
    (cycleComponentSheafClass A ((fst A Y).left x) himage)]
  congr 1
  exact (ccm16_supportedComparison_forget A
    (cycleComponentAnalyticClosedSupport A ((fst A Y).left x)) (2 * q)
    (cycleComponentSupportedInjectiveClass A ((fst A Y).left x) himage)).trans
      (bh11_cupComparison_eq_raw A (2 * q)
        (cycleComponentSheafClass A ((fst A Y).left x) himage)).symm

#print axioms s4_selected_projection_prime_multiple

end HodgeLean.Foundations.Program
