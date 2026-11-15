import HodgeLean.Foundations.Program.SchoenTransferJ12SupportedPrimeSpan
import HodgeLean.Adapters.CycleClassDivisorProduct3

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupComparison cupProductOf

/-- A cup whose two actual supports meet in one component of the expected codimension is algebraic.
Source: relative cup support and purity; Fulton, Intersection Theory, §19.1. -/
theorem s4_selected_cup_mem_of_prime_support
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S T : Closeds (ComplexPoint X)) (m n s : ℕ) (h : m + n = 2 * s)
    (x : X.left) (hx : Order.coheight x = s)
    (hST : S ⊓ T = cycleComponentAnalyticClosedSupport X x)
    (a : HQ X m) (b : HQ X n)
    (u : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
      (S : Set (ComplexPoint X))ᶜ) m)
    (v : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
      (T : Set (ComplexPoint X))ᶜ) n)
    (hu : relativeCohomologyToAbsolute ℚ _ m u = cupComparison X m a)
    (hv : relativeCohomologyToAbsolute ℚ _ n v = cupComparison X n b) :
    (cupProductOf X).cup h a b ∈ cfd_cycleSpan X s := by
  let c₀ := ccm15_relativeCup (TopCat.of (ComplexPoint X)) S T m n u v
  have hc (R : Closeds (ComplexPoint X)) (hR : S ⊓ T = R)
      (t : ℕ) (ht : m + n = t) :
      relativeCohomologyToAbsolute ℚ
        (TopPair.ofSubset (X := TopCat.of (ComplexPoint X)) (R : Set (ComplexPoint X))ᶜ) t
        (hR ▸ ht ▸ c₀) = cupComparison X t ((cupProductOf X).cup ht a b) := by
    subst R t
    dsimp only [c₀]
    rw [ccm15_relativeCup_absolute, hu, hv, cupComparison_cup]
  exact s4_selected_supported_prime_mem X x s hx _ (hST ▸ h ▸ c₀)
    (hc _ hST _ h)

#print axioms s4_selected_cup_mem_of_prime_support
end HodgeLean.Foundations.Program
