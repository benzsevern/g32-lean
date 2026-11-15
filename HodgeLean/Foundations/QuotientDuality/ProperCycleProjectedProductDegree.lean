import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectedProductCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeDegreeTransport

/-! # Literal source and target degree transports for the actual projected product cap
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual projected ordinary product cap retains the specified normal, source and target degree transports.
Source: properCycle_product_projected_support_cap; relativeHomologyDegreeCast.
HC no distance; AV milestone no distance. -/
theorem properCycle_projected_product_degree
    (E F : Type) [NormedAddCommGroup E] [NormedAddCommGroup F]
    {p p' q q' : ℕ} (eP : p = p') (eQ : q = q')
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of F) ({0} : Set F)ᶜ) p)
    (z : orientationGroup (TopCat.of (E × F)) (p+q) (0,0)) :
    relativeHomologyDegreeCast eQ (properCycle_product_projected_support_cap E F p q a z) =
      properCycle_product_projected_support_cap E F p' q' (eP ▸ a)
        (relativeHomologyDegreeCast (congrArg₂ Nat.add eP eQ) z) := by
  subst p'
  subst q'
  rfl

end HodgeLean.Foundations.QuotientDuality
