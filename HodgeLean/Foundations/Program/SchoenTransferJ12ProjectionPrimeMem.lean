import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionMultiple
import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionZero

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Projection of each actual prime cycle class is an algebraic class in the expected degree.
Source: Fulton, Intersection Theory, §19.1, linearity of the cycle class map and proper projection. -/
theorem s4_selected_projection_prime_mem
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d s q : ℕ) (hY : TopologicalSpace.dim Y.left = d)
    (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) (h : 2 * s = 2 * d + 2 * q)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = s) :
    s4_selected_projection A Y d (2 * q) I
      (HQ.castEquiv (A ⊗ Y) h (cycleComponentSheafClass (A ⊗ Y) x hx)) ∈
      cfd_cycleSpan A q := by
  classical
  by_cases himage : Order.coheight ((fst A Y).left x) = q
  · obtain ⟨r, hr⟩ := s4_selected_projection_prime_multiple A Y d s q I h x hx himage
    rw [hr]
    refine Submodule.smul_mem _ r ?_
    change cycleComponentSheafClass A ((fst A Y).left x) himage ∈ algebraicCycleClassSpan A q
    have hle : Submodule.span ℚ ({cycleComponentSheafClass A ((fst A Y).left x) himage} :
        Set (HQ A (2 * q))) ≤ algebraicCycleClassSpan A q := by
      unfold algebraicCycleClassSpan
      exact le_sSup ⟨(fst A Y).left x, himage, rfl⟩
    exact hle (Submodule.subset_span (Set.mem_singleton _))
  · rw [s4_selected_projection_prime_zero A Y d s q hY I h x hx himage]
    exact Submodule.zero_mem _

#print axioms s4_selected_projection_prime_mem

end HodgeLean.Foundations.Program
