import HodgeLean.Foundations.BundleResolution.ChernChartDomainPairHelpers

/-! # Actual chart and base-domain cap square

The original chart pair coordinates identify the actual inverse-image
domain cap map with chart cap followed by the chart base projection.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex Bundle TopologicalSpace AlgebraicTopology AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

variable {B : Type} [TopologicalSpace B] {k : ℕ} (E : I1ComplexBundle B k)
variable (e : Trivialization (Fin k → ℂ)
  (TotalSpace.proj : TotalSpace (Fin k → ℂ) E.fibre → B)) [e.IsLinear ℂ]

theorem i1_chartDomainEvenCapExtendedMap_square
    (φ : RelativeCocycle ℚ
      (TopPair.ofSubset (X := i1_totalSpace k E.fibre) (i1_zeroSupport k E.fibre)ᶜ) (2 * k)) :
    HomologicalComplex.extendMap ((relativeChainFunctor ℚ).map (i1_chartDomainPairIso E e).hom)
        (ComplexShape.embeddingUpIntLE (2 * k : ℕ)) ≫
      i1_domainEvenCapExtendedMap (i1_totalSpace k E.fibre) (TopCat.of B)
        (TopCat.ofHom (i1_complexBundleTotalProjection E)) (i1_zeroSupport k E.fibre)ᶜ e.baseSet k φ =
    i1_evenRelativeCapExtendedChainMap (i1_chartPair k E.fibre e) k
        (i1_relativeCocyclePullback (i1_chartInclusion k E.fibre e) (2 * k) φ).val
        (i1_relativeCocyclePullback (i1_chartInclusion k E.fibre e) (2 * k) φ).property ≫
      HomologicalComplex.extendMap (singularChainComplexMap ℚ (i1_chartBaseProjection E e))
        (ComplexShape.embeddingUpIntLE 0) := by
  let eP := i1_chartDomainPairIso E e
  let φU := i1_relativeCocyclePullback
    (i1_subsetRelativePairInclusion (i1_totalSpace k E.fibre) (i1_zeroSupport k E.fibre)ᶜ
      ((TopCat.ofHom (i1_complexBundleTotalProjection E)) ⁻¹' e.baseSet)) (2 * k) φ
  let φC := i1_relativeCocyclePullback (i1_chartInclusion k E.fibre e) (2 * k) φ
  have hφ : i1_relativeCocyclePullback eP.hom (2 * k) φU = φC :=
    i1_chartDomainPairIso_cocycle E e (2 * k) φ
  have hc := i1_evenRelativeCapExtendedChainMap_naturality eP.hom k φU
  rw [hφ] at hc
  let pu := HomologicalComplex.extendMap
    (singularChainComplexMap ℚ (i1_domainBaseProjection (i1_totalSpace k E.fibre) (TopCat.of B)
      (TopCat.ofHom (i1_complexBundleTotalProjection E)) (i1_zeroSupport k E.fibre)ᶜ e.baseSet))
    (ComplexShape.embeddingUpIntLE 0)
  have he : HomologicalComplex.extendMap (singularChainComplexMap ℚ (TopPair.Hom.fst eP.hom))
        (ComplexShape.embeddingUpIntLE 0) ≫ pu =
      HomologicalComplex.extendMap (singularChainComplexMap ℚ (i1_chartBaseProjection E e))
        (ComplexShape.embeddingUpIntLE 0) := by
    dsimp only [pu]
    rw [← HomologicalComplex.extendMap_comp]
    apply congrArg (fun q => HomologicalComplex.extendMap q (ComplexShape.embeddingUpIntLE 0))
    let C : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} ℚ) ℕ :=
      (singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
    change C.map (TopPair.Hom.fst eP.hom) ≫ C.map
      (i1_domainBaseProjection (i1_totalSpace k E.fibre) (TopCat.of B)
        (TopCat.ofHom (i1_complexBundleTotalProjection E)) (i1_zeroSupport k E.fibre)ᶜ e.baseSet) =
      C.map (i1_chartBaseProjection E e)
    rw [← C.map_comp]
    exact congrArg C.map (i1_chartDomainPairIso_comp_projection E e)
  dsimp only [i1_domainEvenCapExtendedMap]
  rw [← Category.assoc, hc, Category.assoc, he]

end HodgeLean.Foundations.BundleResolution
