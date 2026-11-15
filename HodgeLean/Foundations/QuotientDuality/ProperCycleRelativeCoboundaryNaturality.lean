import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeCochainNaturality

/-! # Actual relative coboundary and pullback -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal relative cochain pullback commutes with the original coboundary.
Source: Hatcher, Algebraic Topology, section 3.1, induced relative cochain maps.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_coboundary_naturality
    {P Q : TopPair.{0}} (f : P ⟶ Q) (p : ℕ) (φ : RelativeCochain ℚ Q p) :
    relativeCoboundary ℚ P p ((((relativeChainFunctor ℚ).map f).f p).hom.dualMap φ) =
      (((relativeChainFunctor ℚ).map f).f (p + 1)).hom.dualMap
        (relativeCoboundary ℚ Q p φ) := by
  ext c
  exact congrArg φ (ConcreteCategory.congr_hom (((relativeChainFunctor ℚ).map f).comm (p + 1) p) c).symm

end HodgeLean.Foundations.QuotientDuality
