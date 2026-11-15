import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionPrimeMem

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] s4_selected_projection algebraicCycleClassSpan

/-- The actual finite-fibre projection preserves the rational algebraic cycle span.
Source: Fulton, Intersection Theory, §19.1, additivity of cycle classes and proper projection. -/
theorem s4_selected_projection_span
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d s q : ℕ) (hY : TopologicalSpace.dim Y.left = d)
    (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) (h : 2 * s = 2 * d + 2 * q) :
    (cfd_cycleSpan (A ⊗ Y) s).map
        ((s4_selected_projection A Y d (2 * q) I).comp
          (HQ.castEquiv (A ⊗ Y) h).toLinearMap) ≤ cfd_cycleSpan A q := by
  apply Submodule.map_le_iff_le_comap.mpr
  change algebraicCycleClassSpan (A ⊗ Y) s ≤ _
  rw [algebraicCycleClassSpan]
  refine sSup_le ?_
  rintro _ ⟨x, hx, rfl⟩
  apply (Submodule.span_singleton_le_iff_mem _ _).mpr
  exact s4_selected_projection_prime_mem A Y d s q hY I h x hx

#print axioms s4_selected_projection_span

end HodgeLean.Foundations.Program
