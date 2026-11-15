import HodgeLean.Foundations.QuotientDuality.ProperCycleUnionRelativeSupportCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleTriadLocalHomology
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeSubsetEquality

/-! # Original ordinary product support source and its literal point pair
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original complement-union support identification followed by the specified original punctured-product subset equality.
Source: properCycle_support_complement_union_iso; properCycle_product_puncture_union.
HC no distance; AV milestone no distance. -/
def properCycle_product_support_point_pair_iso
    (E F : Type) [TopologicalSpace E] [Zero E] [TopologicalSpace F] [Zero F] :
    TopPair.ofSubset (X := TopCat.of (E × F))
      ((Prod.snd ⁻¹' ({0} : Set F)) ∩ {z | z.1 = 0})ᶜ ≅
      TopPair.ofSubset (X := TopCat.of (E × F)) ({(0,0)} : Set (E × F))ᶜ :=
  (properCycle_support_complement_union_iso (TopCat.of (E × F))
    (Prod.snd ⁻¹' ({0} : Set F)) {z | z.1 = 0}).symm ≪≫
    eqToIso (congrArg (fun A : Set (E × F) => TopPair.ofSubset (X := TopCat.of (E × F)) A)
      (properCycle_product_puncture_union E F))

end HodgeLean.Foundations.QuotientDuality
