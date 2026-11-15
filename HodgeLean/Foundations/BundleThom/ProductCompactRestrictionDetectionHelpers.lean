import HodgeLean.Foundations.BundleThom.CompactBaseRelativeCoclassDetectionHelpers
import HodgeLean.Foundations.BundleThom.ProductSubsetPairHelpers
import HodgeLean.Foundations.BundleThom.RelativePairIsoCoclassHelpers

/-! # Product coclass detection by actual compact base restrictions

No compactness or local contractibility is imposed on the whole base.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Restrictions of a product normal coclass to every actual compact base subset detect it in every degree.
Source: Hatcher, Algebraic Topology, §2.1 and §3.1, compact support of singular representatives. -/
theorem i1_productCoclass_ext_of_compact_restrictions {B : Type} [TopologicalSpace B]
    (k n : ℕ) (u v : RelativeCohomology ℚ (i1_productNormalPair B k) n)
    (h : ∀ K : Compacts B, relativeCohomologyMap ℚ n
        (i1_productBaseMap k (Subtype.val : K → B) continuous_subtype_val) u =
      relativeCohomologyMap ℚ n
        (i1_productBaseMap k (Subtype.val : K → B) continuous_subtype_val) v) : u = v := by
  apply i1_relativeCoclass_ext_of_compactBase_restrictions
    (TopCat.of (B × (Fin k → ℂ))) {p | p.2 ≠ 0} Prod.fst continuous_fst n u v
  intro K
  apply i1_relativeCohomologyMap_iso_injective (i1_productSubsetPairIso B k (K : Set B)) n
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    i1_productSubsetPairIso_comp_inclusion,
    ← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    i1_productSubsetPairIso_comp_inclusion]
  exact h K

end HodgeLean.Foundations.BundleThom
