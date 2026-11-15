import HodgeLean.Foundations.BundleResolution.ChernChartDomainCapSquareHelpers
import HodgeLean.Foundations.BundleResolution.ChernBundleThomChartChainHelpers
import HodgeLean.Foundations.BundleResolution.ChernChartBaseProjectionHelpers
import HodgeLean.Foundations.BundleThom.RestrictedChartLowHomologyHelpers

/-! # Actual selected Thom cap on chart base domains

The original chart pair and base projection give the actual domain map
its quasi-isomorphism, using the selected normalized global representative.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex Bundle TopologicalSpace AlgebraicTopology AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {k : ℕ} (E : I1ComplexBundle B k)
variable (e : Trivialization (Fin k → ℂ)
  (TotalSpace.proj : TotalSpace (Fin k → ℂ) E.fibre → B)) [e.IsLinear ℂ]

theorem i1_bundleThomCocycle_domain_chart_quasiIso :
    QuasiIso (i1_domainEvenCapExtendedMap (i1_totalSpace k E.fibre) (TopCat.of B)
      (TopCat.ofHom (i1_complexBundleTotalProjection E)) (i1_zeroSupport k E.fibre)ᶜ e.baseSet k
      (i1_bundleThomCocycle E)) := by
  let φC := i1_relativeCocyclePullback (i1_chartInclusion k E.fibre e) (2 * k) (i1_bundleThomCocycle E)
  let c := i1_evenRelativeCapExtendedChainMap (i1_chartPair k E.fibre e) k φC.val φC.property
  let proj := HomologicalComplex.extendMap (singularChainComplexMap ℚ (i1_chartBaseProjection E e))
    (ComplexShape.embeddingUpIntLE 0)
  let u := HomologicalComplex.extendMap ((relativeChainFunctor ℚ).map (i1_chartDomainPairIso E e).hom)
    (ComplexShape.embeddingUpIntLE (2 * k : ℕ))
  let d := i1_domainEvenCapExtendedMap (i1_totalSpace k E.fibre) (TopCat.of B)
    (TopCat.ofHom (i1_complexBundleTotalProjection E)) (i1_zeroSupport k E.fibre)ᶜ e.baseSet k
    (i1_bundleThomCocycle E)
  haveI : QuasiIso c := i1_bundleThomCocycle_chart_evenCap_quasiIso E e
  haveI : QuasiIso proj := (quasiIso_extendMap_iff _ _).mpr (i1_chartBaseProjection_quasiIso E e)
  haveI : IsIso u := by
    change IsIso (((ComplexShape.embeddingUpIntLE (2 * k : ℕ)).extendFunctor (ModuleCat.{0} ℚ)).map
      ((relativeChainFunctor ℚ).map (i1_chartDomainPairIso E e).hom))
    infer_instance
  have he : u ≫ d = c ≫ proj := i1_chartDomainEvenCapExtendedMap_square E e (i1_bundleThomCocycle E)
  haveI : QuasiIso (u ≫ d) := by
    rw [he]
    exact quasiIso_comp c proj
  exact quasiIso_of_comp_left u d

theorem i1_bundleThomCocycle_domain_open_quasiIso (T : Set B) (hT : IsOpen T) (hTe : T ⊆ e.baseSet) :
    QuasiIso (i1_domainEvenCapExtendedMap (i1_totalSpace k E.fibre) (TopCat.of B)
      (TopCat.ofHom (i1_complexBundleTotalProjection E)) (i1_zeroSupport k E.fibre)ᶜ T k
      (i1_bundleThomCocycle E)) := by
  let r := e.restrOpen T hT
  letI : r.IsLinear ℂ := i1_chartRestrOpen_isLinear k E.fibre e T hT
  have hq := i1_bundleThomCocycle_domain_chart_quasiIso E r
  change QuasiIso (i1_domainEvenCapExtendedMap (i1_totalSpace k E.fibre) (TopCat.of B)
    (TopCat.ofHom (i1_complexBundleTotalProjection E)) (i1_zeroSupport k E.fibre)ᶜ (e.baseSet ∩ T) k
    (i1_bundleThomCocycle E)) at hq
  rw [Set.inter_eq_right.mpr hTe] at hq
  exact hq

end HodgeLean.Foundations.BundleResolution
