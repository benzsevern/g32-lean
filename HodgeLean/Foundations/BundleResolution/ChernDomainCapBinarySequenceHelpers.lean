import HodgeLean.Foundations.BundleResolution.ChernDomainCapBinarySquareHelpers
import HodgeLean.Foundations.BundleResolution.ChernExtendedSequenceComparisonHelpers

/-! # Actual binary domain exact-sequence comparisons for even cap

The intersection and middle maps use actual domain cap. The small-chain
union map is induced by their checked signed inclusion square.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.BundleResolution

variable (X Y : TopCat.{0}) (f : X ⟶ Y) (Z : Set X) (U V : Set Y) (k : ℕ)
variable (φ : RelativeCocycle ℚ (TopPair.ofSubset (X := X) Z) (2 * k))

def i1_domainCapBinarySequenceComparison :
    (i1_relativeDomainBinarySequence X Z (f ⁻¹' U) (f ⁻¹' V)).map
        ((ComplexShape.embeddingUpIntLE (2 * k : ℕ)).extendFunctor (ModuleCat ℚ)) ⟶
      (singularMayerVietorisShortComplex Y U V).map
        ((ComplexShape.embeddingUpIntLE 0).extendFunctor (ModuleCat ℚ)) :=
  i1_extendedSequenceComparison _ _
    (i1_rationalChainSequence_extend_shortExact _
      (i1_relativeDomainBinarySequence_shortExact X Z (f ⁻¹' U) (f ⁻¹' V)) (2 * k : ℕ))
    (i1_domainEvenCapExtendedMap X Y f Z (U ∩ V) k φ)
    (i1_extendedBinaryComparison (2 * k : ℕ)
      (i1_domainEvenCapExtendedMap X Y f Z U k φ)
      (i1_domainEvenCapExtendedMap X Y f Z V k φ))
    (i1_domainCapBinaryIntersection_square X Y f Z U V k φ)

theorem i1_domainCapBinarySequenceComparison_delta (i : ℤ) :
    let hS := i1_rationalChainSequence_extend_shortExact _
      (i1_relativeDomainBinarySequence_shortExact X Z (f ⁻¹' U) (f ⁻¹' V)) (2 * k : ℕ)
    let hT := i1_rationalChainSequence_extend_shortExact _
      (singularMayerVietorisShortComplex_shortExact Y U V) 0
    hS.δ i (i + 1) rfl ≫
        homologyMap (i1_domainEvenCapExtendedMap X Y f Z (U ∩ V) k φ) (i + 1) =
      homologyMap (i1_domainCapBinarySequenceComparison X Y f Z U V k φ).τ₃ i ≫
        hT.δ i (i + 1) rfl := by
  dsimp only
  exact HomologicalComplex.HomologySequence.δ_naturality
    (i1_domainCapBinarySequenceComparison X Y f Z U V k φ)
    (i1_rationalChainSequence_extend_shortExact _
      (i1_relativeDomainBinarySequence_shortExact X Z (f ⁻¹' U) (f ⁻¹' V)) (2 * k : ℕ))
    (i1_rationalChainSequence_extend_shortExact _
      (singularMayerVietorisShortComplex_shortExact Y U V) 0) i (i + 1) rfl

end HodgeLean.Foundations.BundleResolution
