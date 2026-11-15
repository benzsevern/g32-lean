import HodgeLean.Foundations.BundleResolution.ChernDomainRebasePairHelpers

/-! # Actual cap comparisons under nested domain coordinates

The relative pair and base homeomorphisms transport the representative
and the actual projection in the inverse-image cap chain map.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

variable (X Y : TopCat.{0}) (f : X ⟶ Y) (Z : Set X) {U W : Set Y} (h : U ⊆ W)

theorem i1_domainEvenCapExtendedMap_rebase_square (k : ℕ)
    (φ : RelativeCocycle ℚ (TopPair.ofSubset (X := X) Z) (2 * k)) :
    HomologicalComplex.extendMap ((relativeChainFunctor ℚ).map (i1_domainRebasePairIso X Y f Z h).hom)
        (ComplexShape.embeddingUpIntLE (2 * k : ℕ)) ≫
      i1_domainEvenCapExtendedMap X Y f Z U k φ =
    i1_domainEvenCapExtendedMap (TopCat.of (f ⁻¹' W)) (TopCat.of W)
        (i1_domainBaseProjection X Y f Z W) {x : f ⁻¹' W | x.val ∈ Z} {w : W | w.val ∈ U} k
        (i1_relativeCocyclePullback (i1_subsetRelativePairInclusion X Z (f ⁻¹' W)) (2 * k) φ) ≫
      HomologicalComplex.extendMap
        (singularChainComplexMap ℚ (TopCat.isoOfHomeo (i1_nestedDomainHomeomorph h)).hom)
        (ComplexShape.embeddingUpIntLE 0) := by
  let XW := TopCat.of (f ⁻¹' W)
  let YW := TopCat.of W
  let fW := i1_domainBaseProjection X Y f Z W
  let ZW : Set XW := {x | x.val ∈ Z}
  let UN : Set YW := {w | w.val ∈ U}
  let eP := i1_domainRebasePairIso X Y f Z h
  let eB : TopCat.of UN ≅ TopCat.of U := TopCat.isoOfHomeo (i1_nestedDomainHomeomorph h)
  let φW := i1_relativeCocyclePullback (i1_subsetRelativePairInclusion X Z (f ⁻¹' W)) (2 * k) φ
  let φU := i1_relativeCocyclePullback (i1_subsetRelativePairInclusion X Z (f ⁻¹' U)) (2 * k) φ
  let φN := i1_relativeCocyclePullback (i1_subsetRelativePairInclusion XW ZW (fW ⁻¹' UN)) (2 * k) φW
  have hφ : i1_relativeCocyclePullback eP.hom (2 * k) φU = φN :=
    i1_domainRebasePairIso_cocycle X Y f Z h (2 * k) φ
  let cu := i1_evenRelativeCapExtendedChainMap (i1_subsetRelativePair X Z (f ⁻¹' U)) k φU.val φU.property
  let cn := i1_evenRelativeCapExtendedChainMap (i1_subsetRelativePair XW ZW (fW ⁻¹' UN)) k φN.val φN.property
  let pu := HomologicalComplex.extendMap
    (singularChainComplexMap ℚ (i1_domainBaseProjection X Y f Z U)) (ComplexShape.embeddingUpIntLE 0)
  let pn := HomologicalComplex.extendMap
    (singularChainComplexMap ℚ (i1_domainBaseProjection XW YW fW ZW UN)) (ComplexShape.embeddingUpIntLE 0)
  let eb := HomologicalComplex.extendMap (singularChainComplexMap ℚ eB.hom) (ComplexShape.embeddingUpIntLE 0)
  have hc := i1_evenRelativeCapExtendedChainMap_naturality eP.hom k φU
  rw [hφ] at hc
  have he : HomologicalComplex.extendMap (singularChainComplexMap ℚ (TopPair.Hom.fst eP.hom))
        (ComplexShape.embeddingUpIntLE 0) ≫ pu = pn ≫ eb := by
    dsimp only [pu, pn, eb]
    rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
    apply congrArg (fun q => HomologicalComplex.extendMap q (ComplexShape.embeddingUpIntLE 0))
    let C : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} ℚ) ℕ :=
      (singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
    change C.map (TopPair.Hom.fst eP.hom) ≫ C.map (i1_domainBaseProjection X Y f Z U) =
      C.map (i1_domainBaseProjection XW YW fW ZW UN) ≫ C.map eB.hom
    rw [← C.map_comp, ← C.map_comp]
    exact congrArg C.map (i1_domainRebasePairIso_comp_projection X Y f Z h)
  change HomologicalComplex.extendMap ((relativeChainFunctor ℚ).map eP.hom)
      (ComplexShape.embeddingUpIntLE (2 * k : ℕ)) ≫ (cu ≫ pu) = (cn ≫ pn) ≫ eb
  rw [← Category.assoc, hc, Category.assoc, he, Category.assoc]

include h in
theorem i1_domainEvenCapExtendedMap_rebase_quasiIso_iff (k : ℕ)
    (φ : RelativeCocycle ℚ (TopPair.ofSubset (X := X) Z) (2 * k)) :
    QuasiIso (i1_domainEvenCapExtendedMap (TopCat.of (f ⁻¹' W)) (TopCat.of W)
      (i1_domainBaseProjection X Y f Z W) {x : f ⁻¹' W | x.val ∈ Z} {w : W | w.val ∈ U} k
      (i1_relativeCocyclePullback (i1_subsetRelativePairInclusion X Z (f ⁻¹' W)) (2 * k) φ)) ↔
      QuasiIso (i1_domainEvenCapExtendedMap X Y f Z U k φ) := by
  let eP := i1_domainRebasePairIso X Y f Z h
  let eB : TopCat.of {w : W | w.val ∈ U} ≅ TopCat.of U :=
    TopCat.isoOfHomeo (i1_nestedDomainHomeomorph h)
  let u := HomologicalComplex.extendMap ((relativeChainFunctor ℚ).map eP.hom)
    (ComplexShape.embeddingUpIntLE (2 * k : ℕ))
  let v := HomologicalComplex.extendMap (singularChainComplexMap ℚ eB.hom)
    (ComplexShape.embeddingUpIntLE 0)
  let a := i1_domainEvenCapExtendedMap (TopCat.of (f ⁻¹' W)) (TopCat.of W)
    (i1_domainBaseProjection X Y f Z W) {x : f ⁻¹' W | x.val ∈ Z} {w : W | w.val ∈ U} k
    (i1_relativeCocyclePullback (i1_subsetRelativePairInclusion X Z (f ⁻¹' W)) (2 * k) φ)
  let b := i1_domainEvenCapExtendedMap X Y f Z U k φ
  haveI : IsIso u := by
    change IsIso (((ComplexShape.embeddingUpIntLE (2 * k : ℕ)).extendFunctor (ModuleCat.{0} ℚ)).map
      ((relativeChainFunctor ℚ).map eP.hom))
    infer_instance
  haveI : IsIso v := by
    change IsIso (((ComplexShape.embeddingUpIntLE 0).extendFunctor (ModuleCat.{0} ℚ)).map
      (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map eB.hom))
    infer_instance
  have he : u ≫ b = a ≫ v := i1_domainEvenCapExtendedMap_rebase_square X Y f Z h k φ
  change QuasiIso a ↔ QuasiIso b
  constructor
  · intro ha
    letI := ha
    haveI : QuasiIso (u ≫ b) := by
      rw [he]
      exact quasiIso_comp a v
    exact quasiIso_of_comp_left u b
  · intro hb
    letI := hb
    haveI : QuasiIso (a ≫ v) := by
      rw [← he]
      exact quasiIso_comp u b
    exact quasiIso_of_comp_right a v

end HodgeLean.Foundations.BundleResolution
