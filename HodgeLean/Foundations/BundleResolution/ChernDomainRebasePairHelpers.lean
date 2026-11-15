import HodgeLean.Foundations.BundleResolution.ChernNestedDomainHomeomorphHelpers
import HodgeLean.Foundations.BundleResolution.ChernDomainCapChainHelpers

/-! # Actual relative pair coordinates for nested inverse-image domains

Flattening the nested total domain retains the specified subspace and
its actual inclusion in the original ambient pair.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

variable (X Y : TopCat.{0}) (f : X ⟶ Y) (Z : Set X) {U W : Set Y} (h : U ⊆ W)

def i1_domainRebasePairIso :
    i1_subsetRelativePair (TopCat.of (f ⁻¹' W)) {x : f ⁻¹' W | x.val ∈ Z}
        ((i1_domainBaseProjection X Y f Z W) ⁻¹' {w : W | w.val ∈ U}) ≅
      i1_subsetRelativePair X Z (f ⁻¹' U) :=
  TopPair.isoOfSubset (i1_nestedDomainHomeomorph (show f ⁻¹' U ⊆ f ⁻¹' W from Set.preimage_mono h))
    (by intro x; rfl)

theorem i1_domainRebasePairIso_comp_inclusion :
    (i1_domainRebasePairIso X Y f Z h).hom ≫ i1_subsetRelativePairInclusion X Z (f ⁻¹' U) =
      i1_subsetRelativePairInclusion (TopCat.of (f ⁻¹' W)) {x : f ⁻¹' W | x.val ∈ Z}
          ((i1_domainBaseProjection X Y f Z W) ⁻¹' {w : W | w.val ∈ U}) ≫
        i1_subsetRelativePairInclusion X Z (f ⁻¹' W) := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

theorem i1_domainRebasePairIso_comp_projection :
    TopPair.Hom.fst (i1_domainRebasePairIso X Y f Z h).hom ≫
        i1_domainBaseProjection X Y f Z U =
      i1_domainBaseProjection (TopCat.of (f ⁻¹' W)) (TopCat.of W)
          (i1_domainBaseProjection X Y f Z W) {x : f ⁻¹' W | x.val ∈ Z} {w : W | w.val ∈ U} ≫
        (TopCat.isoOfHomeo (i1_nestedDomainHomeomorph h)).hom := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

theorem i1_domainRebasePairIso_cocycle (p : ℕ)
    (φ : RelativeCocycle ℚ (TopPair.ofSubset (X := X) Z) p) :
    i1_relativeCocyclePullback (i1_domainRebasePairIso X Y f Z h).hom p
        (i1_relativeCocyclePullback (i1_subsetRelativePairInclusion X Z (f ⁻¹' U)) p φ) =
      i1_relativeCocyclePullback
        (i1_subsetRelativePairInclusion (TopCat.of (f ⁻¹' W)) {x : f ⁻¹' W | x.val ∈ Z}
          ((i1_domainBaseProjection X Y f Z W) ⁻¹' {w : W | w.val ∈ U})) p
        (i1_relativeCocyclePullback (i1_subsetRelativePairInclusion X Z (f ⁻¹' W)) p φ) := by
  rw [i1_relativeCocyclePullback_comp, i1_relativeCocyclePullback_comp,
    i1_domainRebasePairIso_comp_inclusion]

end HodgeLean.Foundations.BundleResolution
