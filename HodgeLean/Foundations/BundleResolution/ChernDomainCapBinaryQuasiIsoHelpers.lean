import HodgeLean.Foundations.BundleResolution.ChernDomainCapBinarySequenceHelpers
import HodgeLean.Foundations.BundleResolution.ChernIntegerBiproductQuasiIsoHelpers

/-! # Actual binary small-chain union cap quasi-isomorphisms

The checked relative and ordinary domain sequences transfer the three
local cap comparisons to the induced actual small-chain union comparison.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.BundleResolution

theorem i1_domainCapBinaryUnion_quasiIso (X Y : TopCat.{0})
    (f : X ⟶ Y) (Z : Set X) (U V : Set Y) (k : ℕ)
    (φ : RelativeCocycle ℚ (TopPair.ofSubset (X := X) Z) (2 * k))
    (hi : QuasiIso (i1_domainEvenCapExtendedMap X Y f Z (U ∩ V) k φ))
    (hu : QuasiIso (i1_domainEvenCapExtendedMap X Y f Z U k φ))
    (hv : QuasiIso (i1_domainEvenCapExtendedMap X Y f Z V k φ)) :
    QuasiIso (i1_domainCapBinarySequenceComparison X Y f Z U V k φ).τ₃ := by
  letI := hu
  letI := hv
  have hm := i1_extendedBinaryComparison_quasiIso (2 * k : ℕ)
    (i1_domainEvenCapExtendedMap X Y f Z U k φ)
    (i1_domainEvenCapExtendedMap X Y f Z V k φ)
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    (i1_domainCapBinarySequenceComparison X Y f Z U V k φ)
    (i1_rationalChainSequence_extend_shortExact _
      (i1_relativeDomainBinarySequence_shortExact X Z (f ⁻¹' U) (f ⁻¹' V)) (2 * k : ℕ))
    (i1_rationalChainSequence_extend_shortExact _
      (singularMayerVietorisShortComplex_shortExact Y U V) 0) hi hm

end HodgeLean.Foundations.BundleResolution
