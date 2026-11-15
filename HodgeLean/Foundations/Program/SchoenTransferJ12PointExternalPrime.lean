import HodgeLean.Foundations.Program.SchoenTransferJ12PointExternalSupport
import HodgeLean.Foundations.Program.SchoenTransferJ12GraphPointCodimension
import HodgeLean.Foundations.Program.SchoenTransferJ12SupportedCupSpan
import HodgeLean.Foundations.Program.SchoenTransferJ12RelativePrimePullback

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory TopologicalSpace
open CategoryTheory.CartesianMonoidalCategory
open AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- The external cup of an actual point class and a prime class lies in the product cycle span.
Source: purity on the constant graph component and naturality of relative cup products. -/
theorem s4_selected_point_external_prime_mem
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a d : ℕ) (hA : TopologicalSpace.dim A.left = a)
    (hY : TopologicalSpace.dim Y.left = d)
    (f : Y ⟶ A) (e : ComplexPoint A) (he : ∀ b : ComplexPoint Y, Point.map f b = e)
    (hec : Order.coheight e.underlying = a)
    (z : Y.left) (p : ℕ) (hz : Order.coheight z = p) :
    (cupProductOf (A ⊗ Y)).cup (by omega : 2 * a + 2 * p = 2 * (a + p))
      (homPullback (fst A Y) (2 * a) (cycleComponentSheafClass A e.underlying hec))
      (homPullback (snd A Y) (2 * p) (cycleComponentSheafClass Y z hz)) ∈
        cfd_cycleSpan (A ⊗ Y) (a + p) := by
  have hgc : Order.coheight ((lift f (𝟙 Y)).left z) = ((a + p : ℕ) : ℕ∞) := by
    simpa only [Nat.cast_add] using s4_selected_graph_point_codimension A Y a d hA hY f z p hz
  let u := relativeCohomologyMap ℚ (2 * a)
    (ccm17_preimagePair (TopCat.of (ComplexPoint (A ⊗ Y))) (TopCat.of (ComplexPoint A))
      (Point.continuousMap (fst A Y)) (cycleComponentAnalyticClosedSupport A e.underlying))
    (ccm16_supportedComparison A (cycleComponentAnalyticClosedSupport A e.underlying) (2 * a)
      (cycleComponentSupportedInjectiveClass A e.underlying hec))
  let v := relativeCohomologyMap ℚ (2 * p)
    (ccm17_preimagePair (TopCat.of (ComplexPoint (A ⊗ Y))) (TopCat.of (ComplexPoint Y))
      (Point.continuousMap (snd A Y)) (cycleComponentAnalyticClosedSupport Y z))
    (ccm16_supportedComparison Y (cycleComponentAnalyticClosedSupport Y z) (2 * p)
      (cycleComponentSupportedInjectiveClass Y z hz))
  apply s4_selected_cup_mem_of_prime_support (A ⊗ Y)
    (ccm4_inverseAnalyticSupport (fst A Y) (cycleComponentAnalyticClosedSupport A e.underlying))
    (ccm4_inverseAnalyticSupport (snd A Y) (cycleComponentAnalyticClosedSupport Y z))
    (2 * a) (2 * p) (a + p) _ ((lift f (𝟙 Y)).left z) hgc
    (s4_selected_point_external_support A Y f e he z) (u := u) (v := v)
  · exact s4_selected_relative_prime_pullback (A ⊗ Y) A (fst A Y) a e.underlying hec
  · exact s4_selected_relative_prime_pullback (A ⊗ Y) Y (snd A Y) p z hz

#print axioms s4_selected_point_external_prime_mem
end HodgeLean.Foundations.Program
