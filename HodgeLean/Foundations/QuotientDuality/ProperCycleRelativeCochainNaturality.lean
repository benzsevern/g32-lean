import HodgeLean.Foundations.QuotientDuality.ProperCycleSamePairCapProjection
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance

/-! # Actual relative cochain pullback and the ambient cochain comparison -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Pullback through the literal relative chain map commutes with passage to the original ambient cochain.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.1, relative chains and induced cochains.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_cochain_to_absolute_naturality
    {P Q : TopPair.{0}} (f : P ⟶ Q) (p : ℕ) (φ : RelativeCochain ℚ Q p) :
    relativeCochainToAbsolute ℚ P p
      ((((relativeChainFunctor ℚ).map f).f p).hom.dualMap φ) =
      AlgebraicTopology.Simplicial.cochainMap ℚ (TopCat.toSSet.map (TopPair.Hom.fst f)) p
        (relativeCochainToAbsolute ℚ Q p φ) := by
  ext c
  have hc := ConcreteCategory.congr_hom
    (congrArg (fun g : SingularChainComplex ℚ P.fst ⟶ (relativeChainFunctor ℚ).obj Q => g.f p) (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f)) c
  exact congrArg φ hc

end HodgeLean.Foundations.QuotientDuality
