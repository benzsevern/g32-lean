import HodgeLean.Foundations.Program.CompensationAssemblySpan2Local
import HodgeLean.Foundations.Program.SchoenTransferJ12CorrespondenceAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupComparison

/-- A rational class supported on an actual component in its first support degree is algebraic.
Source: purity and the rational rank-one normal class, as in Fulton, Intersection Theory, §19.1. -/
theorem s4_selected_supported_prime_mem
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) (p : ℕ) (hx : Order.coheight x = p)
    (a : HQ X (2 * p))
    (c : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
      ((cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X))ᶜ)) (2 * p))
    (hc : relativeCohomologyToAbsolute ℚ _ (2 * p) c = cupComparison X (2 * p) a) :
    a ∈ cfd_cycleSpan X p := by
  obtain ⟨r, hr⟩ := cq_span_relative_multiple X x p hx c
  have ha : a = r • cycleComponentSheafClass X x hx := by
    apply (cupComparison X (2 * p)).injective
    rw [← hc, hr, map_smul]
    rw [(cupComparison X (2 * p)).map_smul]
    congr 1
    exact (ccm16_supportedComparison_forget X (cycleComponentAnalyticClosedSupport X x)
      (2 * p) (cycleComponentSupportedInjectiveClass X x hx)).trans
      (bh11_cupComparison_eq_raw X (2 * p) (cycleComponentSheafClass X x hx)).symm
  rw [ha]
  apply Submodule.smul_mem
  change cycleComponentSheafClass X x hx ∈ algebraicCycleClassSpan X p
  apply (show Submodule.span ℚ ({cycleComponentSheafClass X x hx} : Set (HQ X (2 * p))) ≤
    algebraicCycleClassSpan X p from le_sSup ⟨x, hx, rfl⟩)
  exact Submodule.subset_span (Set.mem_singleton _)

#print axioms s4_selected_supported_prime_mem
end HodgeLean.Foundations.Program
