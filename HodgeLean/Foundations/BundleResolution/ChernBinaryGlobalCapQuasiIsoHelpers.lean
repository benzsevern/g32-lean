import HodgeLean.Foundations.BundleResolution.ChernDomainCapAugmentationSquareHelpers
import HodgeLean.Foundations.BundleResolution.ChernDomainCapBinaryQuasiIsoHelpers

/-! # Global actual cap through a binary open cover

The actual augmentation square and the actual open-cover small-chain
quasi-isomorphisms transfer binary local cap comparisons to global cap.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.BundleResolution

theorem i1_globalEvenCapExtendedMap_quasiIso_of_binary_cover (X Y : TopCat.{0})
    (f : X ⟶ Y) (Z : Set X) (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (k : ℕ)
    (φ : RelativeCocycle ℚ (TopPair.ofSubset (X := X) Z) (2 * k))
    (hi : QuasiIso (i1_domainEvenCapExtendedMap X Y f Z (U ∩ V) k φ))
    (hu : QuasiIso (i1_domainEvenCapExtendedMap X Y f Z U k φ))
    (hv : QuasiIso (i1_domainEvenCapExtendedMap X Y f Z V k φ)) :
    QuasiIso (i1_globalEvenCapExtendedMap X Y f Z k φ) := by
  let u := HomologicalComplex.extendMap
    (i1_relativeSmallChainComparison X Z
      (i1_singularSubsetRange X (f ⁻¹' U) ⊔ i1_singularSubsetRange X (f ⁻¹' V)))
    (ComplexShape.embeddingUpIntLE (2 * k : ℕ))
  let v := HomologicalComplex.extendMap (twoSubsetSmallChainInclusion Y U V)
    (ComplexShape.embeddingUpIntLE 0)
  let r := (i1_domainCapBinarySequenceComparison X Y f Z U V k φ).τ₃
  let g := i1_globalEvenCapExtendedMap X Y f Z k φ
  have hX : f ⁻¹' U ∪ f ⁻¹' V = Set.univ := by
    rw [← Set.preimage_union, hcover, Set.preimage_univ]
  haveI : QuasiIso u := (quasiIso_extendMap_iff _ _).mpr
    (i1_binaryRelativeSmallChainComparison_quasiIso X Z (f ⁻¹' U) (f ⁻¹' V)
      (hU.preimage f.hom.continuous) (hV.preimage f.hom.continuous) hX)
  have hb : QuasiIso (twoSubsetSmallChainInclusion Y U V) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact twoSubsetSmallChainInclusion_homology_isIso Y U V hU hV hcover n
  haveI : QuasiIso v := (quasiIso_extendMap_iff _ _).mpr hb
  haveI : QuasiIso r := i1_domainCapBinaryUnion_quasiIso X Y f Z U V k φ hi hu hv
  have he : u ≫ g = r ≫ v := i1_domainCapBinaryUnion_augmentation X Y f Z U V k φ
  haveI : QuasiIso (u ≫ g) := by
    rw [he]
    exact quasiIso_comp r v
  exact quasiIso_of_comp_left u g

end HodgeLean.Foundations.BundleResolution
