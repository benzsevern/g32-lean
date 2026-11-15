import HodgeLean.Foundations.BundleThom.ProductSubsetPairHelpers
import HodgeLean.Foundations.BundleThom.RelativePairIsoCoclassHelpers
import HodgeLean.Foundations.BundleThom.ActualIntersectionCoclassDetectionHelpers
import HodgeLean.Foundations.BundleThom.RelativeHomologySuccessorVanishingHelpers

/-! # Coclass detection by actual open base covers of product normal pairs

The preceding-degree input is on the product over the actual base intersection.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Actual product restrictions over a binary open base cover detect successor-degree coclasses when preceding-degree intersection homology vanishes.
Source: Hatcher, Algebraic Topology, §2.2 and §3.1, relative Mayer–Vietoris. -/
theorem i1_productBinaryCoclass_ext {B : Type} [TopologicalSpace B] (k : ℕ)
    (U V : Set B) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ) (hz : IsZero (RelativeHomology ℚ (i1_productNormalPair ↥(U ∩ V) k) n))
    (u v : RelativeCohomology ℚ (i1_productNormalPair B k) (n + 1))
    (hu : relativeCohomologyMap ℚ (n + 1)
        (i1_productBaseMap k (Subtype.val : U → B) continuous_subtype_val) u =
      relativeCohomologyMap ℚ (n + 1)
        (i1_productBaseMap k (Subtype.val : U → B) continuous_subtype_val) v)
    (hv : relativeCohomologyMap ℚ (n + 1)
        (i1_productBaseMap k (Subtype.val : V → B) continuous_subtype_val) u =
      relativeCohomologyMap ℚ (n + 1)
        (i1_productBaseMap k (Subtype.val : V → B) continuous_subtype_val) v) : u = v := by
  have hrestr (S : Set B)
      (h : relativeCohomologyMap ℚ (n + 1)
        (i1_productBaseMap k (Subtype.val : S → B) continuous_subtype_val) u =
      relativeCohomologyMap ℚ (n + 1)
        (i1_productBaseMap k (Subtype.val : S → B) continuous_subtype_val) v) :
      relativeCohomologyMap ℚ (n + 1)
        (i1_subsetRelativePairInclusion (TopCat.of (B × (Fin k → ℂ)))
          {p | p.2 ≠ 0} (Prod.fst ⁻¹' S)) u =
      relativeCohomologyMap ℚ (n + 1)
        (i1_subsetRelativePairInclusion (TopCat.of (B × (Fin k → ℂ)))
          {p | p.2 ≠ 0} (Prod.fst ⁻¹' S)) v := by
    apply i1_relativeCohomologyMap_iso_injective (i1_productSubsetPairIso B k S) (n + 1)
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
      i1_productSubsetPairIso_comp_inclusion,
      ← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
      i1_productSubsetPairIso_comp_inclusion]
    exact h
  apply i1_actualIntersectionBinaryCoclass_ext (TopCat.of (B × (Fin k → ℂ)))
    {p | p.2 ≠ 0} (Prod.fst ⁻¹' U) (Prod.fst ⁻¹' V)
    (hU.preimage continuous_fst) (hV.preimage continuous_fst) ?_ n ?_ u v
    (hrestr U hu) (hrestr V hv)
  · rw [← Set.preimage_union, hcover, Set.preimage_univ]
  · change IsZero (RelativeHomology ℚ
      (i1_subsetRelativePair (TopCat.of (B × (Fin k → ℂ))) {p | p.2 ≠ 0}
        (Prod.fst ⁻¹' (U ∩ V))) n)
    exact hz.of_iso ((relativeHomologyFunctor ℚ n).mapIso
      (i1_productSubsetPairIso B k (U ∩ V))).symm

end HodgeLean.Foundations.BundleThom
