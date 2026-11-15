import HodgeLean.Foundations.BundleResolution.ChernRelativeClassNaturalityHelpers

/-! # Composition of actual relative cocycle pullbacks

Representatives restricted through nested actual domains agree as cochains,
with the same relative quotient maps used by the cap comparison.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleResolution

theorem i1_relativeCocyclePullback_comp {P Q R : TopPair}
    (f : P ⟶ Q) (g : Q ⟶ R) (p : ℕ) (φ : RelativeCocycle ℚ R p) :
    i1_relativeCocyclePullback f p (i1_relativeCocyclePullback g p φ) =
      i1_relativeCocyclePullback (f ≫ g) p φ := by
  apply Subtype.ext
  ext c
  change φ.val (((relativeChainFunctor ℚ).map g).f p
    (((relativeChainFunctor ℚ).map f).f p c)) =
    φ.val (((relativeChainFunctor ℚ).map (f ≫ g)).f p c)
  rw [(relativeChainFunctor ℚ).map_comp]
  rfl

end HodgeLean.Foundations.BundleResolution
