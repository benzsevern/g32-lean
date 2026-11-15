import HodgeLean.Foundations.BundleResolution.ChernDomainCapChainHelpers

/-! # Nested-domain naturality for the actual cap comparisons

The same global cocycle restricts through the actual pair inclusions,
and the continuous domain projections commute with the base inclusions.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

theorem i1_domainEvenCapExtendedMap_naturality (X Y : TopCat.{0})
    (f : X ⟶ Y) (Z : Set X) {U V : Set Y} (h : U ⊆ V) (k : ℕ)
    (φ : RelativeCocycle ℚ (TopPair.ofSubset (X := X) Z) (2 * k)) :
    HomologicalComplex.extendMap
        ((relativeChainFunctor ℚ).map (i1_subsetRelativePairMap X Z (Set.preimage_mono h)))
        (ComplexShape.embeddingUpIntLE (2 * k : ℕ)) ≫
      i1_domainEvenCapExtendedMap X Y f Z V k φ =
    i1_domainEvenCapExtendedMap X Y f Z U k φ ≫
      HomologicalComplex.extendMap
        (singularChainComplexMap ℚ (TopCat.ofHom
          (⟨Set.inclusion h, continuous_inclusion h⟩ : C(U, V))))
        (ComplexShape.embeddingUpIntLE 0) := by
  let a := i1_subsetRelativePairMap X Z (show f ⁻¹' U ⊆ f ⁻¹' V from Set.preimage_mono h)
  let b : TopCat.of U ⟶ TopCat.of V :=
    TopCat.ofHom (⟨Set.inclusion h, continuous_inclusion h⟩ : C(U, V))
  let φU := i1_relativeCocyclePullback (i1_subsetRelativePairInclusion X Z (f ⁻¹' U)) (2 * k) φ
  let φV := i1_relativeCocyclePullback (i1_subsetRelativePairInclusion X Z (f ⁻¹' V)) (2 * k) φ
  have hφ : i1_relativeCocyclePullback a (2 * k) φV = φU := by
    dsimp only [φU, φV, a]
    rw [i1_relativeCocyclePullback_comp, i1_subsetRelativePairMap_comp_inclusion]
  let cu := i1_evenRelativeCapExtendedChainMap (i1_subsetRelativePair X Z (f ⁻¹' U)) k φU.val φU.property
  let cv := i1_evenRelativeCapExtendedChainMap (i1_subsetRelativePair X Z (f ⁻¹' V)) k φV.val φV.property
  let pu := HomologicalComplex.extendMap
    (singularChainComplexMap ℚ (i1_domainBaseProjection X Y f Z U)) (ComplexShape.embeddingUpIntLE 0)
  let pv := HomologicalComplex.extendMap
    (singularChainComplexMap ℚ (i1_domainBaseProjection X Y f Z V)) (ComplexShape.embeddingUpIntLE 0)
  let bi := HomologicalComplex.extendMap (singularChainComplexMap ℚ b) (ComplexShape.embeddingUpIntLE 0)
  have hc := i1_evenRelativeCapExtendedChainMap_naturality a k φV
  rw [hφ] at hc
  have he : HomologicalComplex.extendMap (singularChainComplexMap ℚ (TopPair.Hom.fst a))
        (ComplexShape.embeddingUpIntLE 0) ≫ pv = pu ≫ bi := by
    dsimp only [pv, pu, bi]
    rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
    apply congrArg (fun q => HomologicalComplex.extendMap q (ComplexShape.embeddingUpIntLE 0))
    let C : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} ℚ) ℕ :=
      (singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
    change C.map (TopPair.Hom.fst a) ≫ C.map (i1_domainBaseProjection X Y f Z V) =
      C.map (i1_domainBaseProjection X Y f Z U) ≫ C.map b
    rw [← C.map_comp, ← C.map_comp]
    rfl
  change HomologicalComplex.extendMap ((relativeChainFunctor ℚ).map a)
      (ComplexShape.embeddingUpIntLE (2 * k : ℕ)) ≫ (cv ≫ pv) = (cu ≫ pu) ≫ bi
  rw [← Category.assoc, hc, Category.assoc, he, Category.assoc]

end HodgeLean.Foundations.BundleResolution
