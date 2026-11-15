import HodgeLean.Foundations.BundleResolution.ChernChartThomMultiplicationHelpers
import HodgeLean.Foundations.BundleResolution.ChernThomMultiplicationHelpers
import HodgeLean.Foundations.BundleResolution.ChernDomainCapChainHelpers

/-! # Actual chart pair and inverse-image base-domain coordinates

The original chart source equality gives the pair isomorphism, retaining
the actual bundle zero complement and the original base projection.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Bundle TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

variable {B : Type} [TopologicalSpace B] {k : ℕ} (E : I1ComplexBundle B k)
variable (e : Trivialization (Fin k → ℂ)
  (TotalSpace.proj : TotalSpace (Fin k → ℂ) E.fibre → B)) [e.IsLinear ℂ]

def i1_chartDomainPairIso : i1_chartPair k E.fibre e ≅
    i1_subsetRelativePair (i1_totalSpace k E.fibre) (i1_zeroSupport k E.fibre)ᶜ
      ((TopCat.ofHom (i1_complexBundleTotalProjection E)) ⁻¹' e.baseSet) :=
  TopPair.isoOfSubset (Homeomorph.setCongr e.source_eq) (by intro v; rfl)

theorem i1_chartDomainPairIso_comp_inclusion :
    (i1_chartDomainPairIso E e).hom ≫
        i1_subsetRelativePairInclusion (i1_totalSpace k E.fibre) (i1_zeroSupport k E.fibre)ᶜ
          ((TopCat.ofHom (i1_complexBundleTotalProjection E)) ⁻¹' e.baseSet) =
      i1_chartInclusion k E.fibre e := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

theorem i1_chartDomainPairIso_comp_projection :
    TopPair.Hom.fst (i1_chartDomainPairIso E e).hom ≫
        i1_domainBaseProjection (i1_totalSpace k E.fibre) (TopCat.of B)
          (TopCat.ofHom (i1_complexBundleTotalProjection E)) (i1_zeroSupport k E.fibre)ᶜ e.baseSet =
      i1_chartBaseProjection E e := by
  apply ConcreteCategory.hom_ext
  intro v
  rfl

theorem i1_chartDomainPairIso_cocycle (p : ℕ)
    (φ : RelativeCocycle ℚ
      (TopPair.ofSubset (X := i1_totalSpace k E.fibre) (i1_zeroSupport k E.fibre)ᶜ) p) :
    i1_relativeCocyclePullback (i1_chartDomainPairIso E e).hom p
      (i1_relativeCocyclePullback
        (i1_subsetRelativePairInclusion (i1_totalSpace k E.fibre) (i1_zeroSupport k E.fibre)ᶜ
          ((TopCat.ofHom (i1_complexBundleTotalProjection E)) ⁻¹' e.baseSet)) p φ) =
      i1_relativeCocyclePullback (i1_chartInclusion k E.fibre e) p φ := by
  rw [i1_relativeCocyclePullback_comp, i1_chartDomainPairIso_comp_inclusion]

end HodgeLean.Foundations.BundleResolution
