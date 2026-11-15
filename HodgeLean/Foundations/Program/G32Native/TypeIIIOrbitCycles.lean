import HodgeLean.Foundations.Program.G32Native.TypeIIIOrbitPullback
import HodgeLean.Foundations.AbelianQuotient.Basic
import HodgeLean.Adapters.CycleClassPullbackSpan

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations

namespace HodgeLean.Foundations.Program.TypeIIIPaper

/-- A cycle class, with its codimension selected by the cycle-class map, lies in the cycle span. -/
theorem cycleClass_mem_span (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (q : ℕ) (c : AlgebraicCycle X.left ℚ) :
    ccm3_cycleClass X q c ∈ algebraicCycleClassSpan X q := by
  unfold ccm3_cycleClass
  refine finsum_induction (· ∈ algebraicCycleClassSpan X q) (Submodule.zero_mem _)
    (fun _ _ ↦ Submodule.add_mem _) (fun z ↦ Submodule.smul_mem _ _ ?_)
  exact (le_sSup ⟨z.1, z.2, rfl⟩ : Submodule.span ℚ {cycleComponentSheafClass X z.1 z.2} ≤
    algebraicCycleClassSpan X q) (Submodule.mem_span_singleton_self _)

/-- Smooth morphisms preserve the rational algebraic cycle span by pullback. -/
theorem smoothPullback_span {X Y : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ X) [Smooth f.left] (q : ℕ) :
    (algebraicCycleClassSpan X q).map (homPullback f (2*q)) ≤
      algebraicCycleClassSpan Y q := by
  apply Submodule.map_le_iff_le_comap.mpr
  rw [algebraicCycleClassSpan]
  refine sSup_le ?_
  rintro _ ⟨x, hx, rfl⟩
  apply (Submodule.span_singleton_le_iff_mem _ _).mpr
  change homPullback f (2*q) (cycleComponentSheafClass X x hx) ∈
    algebraicCycleClassSpan Y q
  rw [ccm6_homPullback_prime f q x hx]
  exact cycleClass_mem_span Y q _

#print axioms cycleClass_mem_span
#print axioms smoothPullback_span
end HodgeLean.Foundations.Program.TypeIIIPaper
