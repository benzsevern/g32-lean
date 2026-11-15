import HodgeLean.Foundations.BundleResolution.ChernDomainCapNaturalityHelpers
import HodgeLean.Foundations.BundleResolution.ChernExtendedBinaryComparisonHelpers
import HodgeLean.Foundations.BundleResolution.ChernRelativeDomainSequenceHelpers
import HodgeLean.Foundations.Singular.MayerVietoris

/-! # Actual binary domain intersection square for even cap

The signed relative domain inclusions and the signed base inclusions
commute with the actual cap maps selected from one global cocycle.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.BundleResolution

theorem i1_domainCapBinaryIntersection_square (X Y : TopCat.{0})
    (f : X ⟶ Y) (Z : Set X) (U V : Set Y) (k : ℕ)
    (φ : RelativeCocycle ℚ (TopPair.ofSubset (X := X) Z) (2 * k)) :
    i1_domainEvenCapExtendedMap X Y f Z (U ∩ V) k φ ≫
        HomologicalComplex.extendMap (singularMayerVietorisShortComplex Y U V).f
          (ComplexShape.embeddingUpIntLE 0) =
      HomologicalComplex.extendMap
          (i1_relativeDomainBinarySequence X Z (f ⁻¹' U) (f ⁻¹' V)).f
          (ComplexShape.embeddingUpIntLE (2 * k : ℕ)) ≫
        i1_extendedBinaryComparison (2 * k : ℕ)
          (i1_domainEvenCapExtendedMap X Y f Z U k φ)
          (i1_domainEvenCapExtendedMap X Y f Z V k φ) := by
  rw [i1_relativeDomainBinarySequence_f]
  symm
  apply i1_extendedBinaryComparison_lift
  · exact i1_domainEvenCapExtendedMap_naturality X Y f Z
      (Set.inter_subset_left : U ∩ V ⊆ U) k φ
  · exact i1_domainEvenCapExtendedMap_naturality X Y f Z
      (Set.inter_subset_right : U ∩ V ⊆ V) k φ

end HodgeLean.Foundations.BundleResolution
